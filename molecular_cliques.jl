begin
	# -------------------------------------------------------------------------
	# here are two algorithms, by removing timeout they become NP Hard 
	# i.e. non approximate. 
	# ( I am using large timeout for NP Hard as some molecules are very large)
	# Complexity Analysis
	# Moon and Moser n vertex graph has atmost 3^(n/3) cliques.
	# -------------------------------------------------------------------------
	using PlutoUI
	# Vinay's Maximal Cliques algorithm:
	const MIN_TIMEOUT = 10  # minimum value of clique detection timeout
	# ------------------------------------------------------------------
	# MolecularGraph.jl, also implements a version for forest by Tomita.
	# https://github.com/mojaie/MolecularGraph.jl/blob/master/src/graph/clique.jl
	# This version implements BronKerbosch variations (without pivot, maxdegree pivot)
	# The worst-case time complexity for generating all maximal cliques and 
	# computational experiments by Etsuji Tomita, Akira Tanaka, Haruhisa Takahashi.
	# ------------------------------------------------------------------
	expiration_timeput(timeout::Real) = UInt64(time_ns() 
											+ timeout * 1_000_000_000_000)
	
	abstract type AbstractCliquesSearch{T} end
	# in order to keep conversions from CliquesSearch to SimpleGraph
	# we need to keep SimpleGraph as first element.
	mutable struct CliquesSearch{T,U} <: AbstractCliquesSearch{T}
	    graph::SimpleGraph{T}
		# Approximate version keeps track of time to expire.
	    expire::Union{UInt64,Nothing} 
	    R::Vector{T}
	    cliques::Vector{U}
	    status::Symbol
	end
	# Clique is a complete subgraph of G.
	# maximal independent set of G = set of vertices of maximal clique of compl_graph(G).
	# Bron–Kerbosch algorithm /  Akkoyunlu (1973) -- Algorithm
	# https://en.wikipedia.org/wiki/Bron%E2%80%93Kerbosch_algorithm
	# Q is empty set that gets build up as clique
	# expand looks at vertices and adds larger connected vertices to Q.
	# -----------------------------------------------------------------
	# algorithm BronKerbosch1(R, P, X) is
    #  if P and X are both empty then
    #     report R as a maximal clique
    #  for each vertex v in P do
    #     BronKerbosch1(R ⋃ {v}, P ⋂ N(v), X ⋂ N(v))
    #     P := P \ {v}
    #     X := X ⋃ {v}
	# ----------------------------------------------------------------
	# In implementation below:
	# R  = state:: AbstractCliquesState starts with {empty}
	# P  = subgraph starts with all vertices.
	# X  = candidate starts with all vertices and we remove vertices
	# ----------------------------------------------------------------
    # to backtrack quickly and not make call into every clique 
	# [pivot is from P ⋃ X]
	# algorithm BronKerbosch2(R, P, X) is
    # if P and X are both empty then
    #    report R as a maximal clique
    # choose a pivot vertex u in P ⋃ X
    # for each vertex v in P \ N(u) do
    #    BronKerbosch2(R ⋃ {v}, P ⋂ N(v), X ⋂ N(v))
    #    P := P \ {v}
    #    X := X ⋃ {v}
	# Instantiate CliquesState
	CliquesSearch{T,U}(g::SimpleGraph{T};
    timeout=MIN_TIMEOUT, kwargs...
	) where {T,U} = CliquesSearch{T,U}(
    g, expiration_timeput(timeout), [], U[], :ongoing)


	function BronKerbosch!(state:: AbstractCliquesSearch, subg, candidate)
	    (state.status == :timedout || state.status == :targetreached) && return
	    if isempty(subg)
	        # Report max clique
			push!(state.cliques, copy(state.R))
	        return
	    end
	    # ----------------------------------------------------------------------
		# Recurse expand by going over all vertices in set, while removing what
		# we have already looked... 
		# we browse vertices while looking at its neighbors.
		# This is Less optimal version as it explores all branches even branches 
		# with non maximal clique. (first algorithm BronKerbosch1)
		# Graphs library provides intersect, neighbors functions.
		# ----------------------------------------------------------------------
	    for node in candidate 
			# Get neighbors of q, candidate is restricted to neighbors of q.
	        nodenbrs = neighbors(state.graph, node)
			# Get unexplore neighbors.
	        candidateq = intersect(candidate, nodenbrs)
			# add this vertex to queue.
	        push!(state.R, node)
			nodecount = length(state.R) + length(candidateq)
			# X ⋂ N(v) 
			subgq = intersect(subg, nodenbrs)
			# We can also check nodecount length with state.maxsofar to limit search.
			# triggers backtracking... when there is nothing further to look.
			if (state isa CliquesSearch)
	            BronKerbosch!(state, subgq, candidateq)
	        end
			# remove processed vertices, from candidate set of vertices.
	        pop!(candidate, node)
			# remove states. backtrack
			# R := R \ {v}
	        pop!(state.R)
	    end
	end
	
	function vinay_all_maximal_cliques(::Type{U}, g::SimpleGraph{T}; kwargs...) where {T,U}
		# place to store our cliques
		state = CliquesSearch{T,U}(g; kwargs...)
		BronKerbosch!(state, Set(vertices(g)), Set(vertices(g)))
		if state.status == :ongoing
			state.status = :done
		end
		return state.cliques, state.status
	end
	# Parameteric initialization for clique finder (defines T).
	vinay_all_maximal_cliques(g::SimpleGraph{T}; kwargs...) where T = vinay_all_maximal_cliques(Vector{T}, g; kwargs...)

	
	#vinay_all_maximal_cliques(cefditoren.graph)


	#########################################
    # Approximate version with pivot.
    # every clique must contain pivot or a non neighborhood of pivot.
    # i.e. if clique so far does not contain non neighborhood of pivot, add pivot to 
    # clique.
    #########################################

    function getpivot(g, subg, candidate)
		pivot = sortstablemax(subg, by=x->degree(g, x))
		return pivot
	end

	function BronKerbosch_approx!(state:: AbstractCliquesSearch, subg, candidate)
	    (state.status == :timedout || state.status == :targetreached) && return
	    if isempty(subg)
	        # Report max clique
			push!(state.cliques, copy(state.R))
	        return
			# No need to keep running if graph is large.
	    elseif state.expire !== nothing && time_ns() > state.expire
	        state.status = :timedout
	        return
	    end
		# Neighbors of pivot are not recursively tested pivot is from P ⋃ X. 
		# P is subgraph.
	    pivot = getpivot(state.graph, subg, candidate)
		# degeneracy -- not use pivot at outermost level of recursion.
		# every subgraph has a vertex with degree d or less.
		# Pick pivot with max degree.
		# copv is P \ N(pivot) -- only iterate over subgraph not in neighborhood 
		# of pivot.
	    candidatewitoutpivotneighbors = setdiff(candidate, neighbors(state.graph, pivot))
		# Recurse expand by going over all vertices in set, while removing what
		# we have already looked... 
		# we browse vertices while looking at its neighbors.
	    for node in candidatewitoutpivotneighbors
			# Get neighbors
	        nodenbrs = neighbors(state.graph, node)
			# Get unexplore neighbors.
	        candidateq = intersect(candidate, nodenbrs)
			# add this vertex to queue.
	        push!(state.R, node)
			nodecount = length(state.R) + length(candidateq)
			# whether clique is already part of neighbors that have been 
			# part of a clique (non maximal sub cliques). 
			# (x intersection neighbors)
			# X ⋂ N(v)
			subgq = intersect(subg, nodenbrs)
			# triggers backtracking... when there is nothing further to look.
	        if (state isa CliquesSearch)
	            BronKerbosch_approx!(state, subgq, candidateq)
	        end
			# remove processed vertices, from candidate set of vertices.
	        pop!(candidate, node)
			# remove states. backtrack
			# R := R \ {v}
	        pop!(state.R)
	    end
	end
	
	function vinay_all_maximal_cliques_approx(::Type{U}, g::SimpleGraph{T}; kwargs...) where {T,U}
		# place to store our cliques
		state = CliquesSearch{T,U}(g; kwargs...)
		BronKerbosch_approx!(state, Set(vertices(g)), Set(vertices(g)))
		if state.status == :ongoing
			state.status = :done
		end
		return state.cliques, state.status
	end
	# Parameteric initialization for clique finder (defines T).
	vinay_all_maximal_cliques_approx(g::SimpleGraph{T}; kwargs...) where T = vinay_all_maximal_cliques_approx(Vector{T}, g; kwargs...)

	
	with_terminal() do 
		p = vinay_all_maximal_cliques(cefditoren.graph)
		p1 = vinay_all_maximal_cliques_approx(cefditoren.graph)
		println("{Non Approximate Call...}\n", p)
		println("[Approximate Call...]\n", p1)
	end
end
