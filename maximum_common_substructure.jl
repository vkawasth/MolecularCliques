### A Pluto.jl notebook ###
# v0.17.7

using Markdown
using InteractiveUtils

# ╔═╡ 8b4b7b1a-8f77-4917-b55c-3f32ddd3bb4f
using Profile, Graphs, MolecularGraph

# ╔═╡ 8ed41278-460b-490c-b691-232418a53a65
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

# ╔═╡ c324c158-d7fa-11ed-0300-93b6975d9deb
md"
# Maximum common substructure

MolecularGraph.jl version: 0.17.1

MolecularGraph.js implements following essential maximum common substructure (MCS) methods for cheminformatics applications.

- Maximum common induced substructure (MCIS)
- Maximum common edge-induced substructure (MCES)
- Connected or disconnected MCS
- Working with larger molecules
- Topological constraint (known as TD-MCS)
"

# ╔═╡ 62d3c057-1c65-44fd-ac25-266bdb26e536
data_dir = let
	# Create data directory
	data_dir = "_data"
	isdir(data_dir) || mkdir(data_dir)
	data_dir
end

# ╔═╡ 29a84294-8ab8-4d93-9d05-adcf67f6c57d
function fetch_mol!(cid, name, datadir)
	url = "https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/cid/$(cid)/SDF"
	dest = joinpath(data_dir, "$(name).mol")
	isfile(dest) || download(url, dest);
	return dest
end

# ╔═╡ 65b40864-4cbc-4122-9b58-cfbecdee34ee
md"
### Maximum common induced substructure (MCIS)

- `disconnected_mcis(mol1, mol2)` calculates maximum common induced (node-induced) substructure (MCIS).
- 'induced' (or specifically 'node-induced') means that the subgraph is defined by a subset of the vertices of the original graph, and the presence or absence of edges between all vertices of the subgraph must match that of the original graph. That also means there is at least one vertex mapping (injection) from the subgraph to the original graph.
- MCS methods in this library returns a result in `Tuple{Dict,Symbol}`.
  - the first element is a mapping of vertex indices between two molecules.
  - the second element is the calculation status. `:done` means that the calculation was successfully finished.
- Unlike substructure match, `MCSResult` have only one of the largest vertex mapping. This is because of the high computational cost of MCS calculation as described below.
- Like substructure match, MCS calculation considers the match between of the atom symbol and the number of pi electron on the atom (not the bond order). This is why the nitrogen atom in the following example does not match (N adjacent to multiple or aromatic bond is treated as sp2 in the default descriptor function).
"

# ╔═╡ 18e3d457-bd9e-418f-a08e-25eefcd02cd0
ldopa = let
	mol = sdftomol(fetch_mol!("6047", "Levodopa", data_dir))
	remove_all_hydrogens!(mol)
	mol
end; nothing

# ╔═╡ 0c2ddc86-71ac-43d1-ae86-71510b216d92
aminocoumarin = let
	mol = sdftomol(fetch_mol!("74217", "3-Aminocoumarin", data_dir))
	remove_all_hydrogens!(mol)
	mol
end; nothing

# ╔═╡ 8b645955-b2ce-4b2a-9793-18a1612e2a75
mcis_result, mcis_status = disconnected_mcis(ldopa, aminocoumarin)

# ╔═╡ 7b38cdb4-7afd-4957-b6d3-116b4bd90d96
let
	nodes1 = collect(keys(mcis_result))
	# induce MCS edges from the vertex mapping
	edges1 = induced_subgraph_edges(ldopa.graph, nodes1)
	svg1 = html_fixed_size(ldopa, 250, 250,
		atomhighlight=nodes1, bondhighlight=edges1, atomindex=true)

	nodes2 = collect(values(mcis_result))
	edges2 = induced_subgraph_edges(aminocoumarin.graph, nodes2)
	svg2 = html_fixed_size(aminocoumarin, 250, 250,
		atomhighlight=nodes2, bondhighlight=edges2, atomindex=true)

	[svg1, svg2]
end

# ╔═╡ 154d878f-230d-4e1a-a8b1-f261e226594a
md"
### Maximum common edge-induced substructure (MCES)

- `disconnected_mces(mol1, mol2)` calculates maximum common edge-induced substructure (MCES).
- Similar to node-induced subgraph, 'edge-induced' means that the subgraph is defined by a subset of the 'edges' of the original graph. Obviously, the vertex set of edge-induced subgraph is a subset of the vertices of the original graph. Also, there is at least one 'edge' mapping (injection) from the subgraph to the original graph.
- In many cases the MCIS size is sufficient as an indicator of the degree of structural match. On the other hand, many chemists may feel MCES is more intuitive than MCIS, so it may worth doing MCES visualization with a slightly higher computational cost.
"

# ╔═╡ 8ac8565c-1f9e-42e7-a90d-705971864955
mces_result, mces_status = disconnected_mces(ldopa, aminocoumarin)

# ╔═╡ 0fbaefff-78f8-4b27-aaf4-b951fe975df2
let
	edges1 = collect(keys(mces_result))
	# induce MCS nodes from the edge mapping
	nodes1, vmap1 = induced_subgraph(ldopa.graph, edges1)
	svg1 = html_fixed_size(ldopa, 250, 250,
		atomhighlight=vmap1[vertices(nodes1)], bondhighlight=edges1, atomindex=true)

	edges2 = collect(values(mces_result))
	nodes2, vmap2 = induced_subgraph(aminocoumarin.graph, edges2)
	svg2 = html_fixed_size(aminocoumarin, 250, 250,
		atomhighlight=vmap2[vertices(nodes2)], bondhighlight=edges2, atomindex=true)

	[svg1, svg2]
end

# ╔═╡ 3c7be77e-6116-4c93-b3c0-a058cdd20a52
md"
### Connected or disconnected MCS

- `connected_mcis(mol1, mol2)` and `connected_mces(mol1, mol2)` also calculates MCIS and MCES but with connection constraint (obtained MCS must be a connected component).
- Connected MCS is much less computationally expensive than disconnected MCS.
- As disconnected MCS does not care the spatial relationship (distance) among matched fragments, connected MCS can be more appropriate option for some kind of applications.
"

# ╔═╡ 0fb4d717-6422-4e1b-a345-a5841d164d9f
conn_mcis_result, conn_mcis_status = connected_mcis(ldopa, aminocoumarin)

# ╔═╡ a0ae8cb9-a5b7-4e8d-834b-3bea0bbcc9de
let
	nodes1 = collect(keys(conn_mcis_result))
	edges1 = induced_subgraph_edges(ldopa.graph, nodes1)
	svg1 = html_fixed_size(ldopa, 250, 250,
		atomhighlight=nodes1, bondhighlight=edges1, atomindex=true)

	nodes2 = collect(values(conn_mcis_result))
	edges2 = induced_subgraph_edges(aminocoumarin.graph, nodes2)
	svg2 = html_fixed_size(aminocoumarin, 250, 250,
		atomhighlight=nodes2, bondhighlight=edges2, atomindex=true)

	[svg1, svg2]
end

# ╔═╡ 8b4b896d-f6e7-427c-84f5-0bcc44eb5fc9
conn_mces_result, conn_mces_status = connected_mces(ldopa, aminocoumarin)

# ╔═╡ 2cdd67cb-35d0-4bab-b8b9-5ce37552398e
let
	edges1 = collect(keys(conn_mces_result))
	nodes1, vmap1 = induced_subgraph(ldopa.graph, edges1)
	svg1 = html_fixed_size(ldopa, 250, 250,
		atomhighlight=vmap1[vertices(nodes1)], bondhighlight=edges1, atomindex=true)

	edges2 = collect(values(conn_mces_result))
	nodes2, vmap2 = induced_subgraph(aminocoumarin.graph, edges2)
	svg2 = html_fixed_size(aminocoumarin, 250, 250,
		atomhighlight=vmap2[vertices(nodes2)], bondhighlight=edges2, atomindex=true)

	[svg1, svg2]
end

# ╔═╡ b7a007c9-8b18-428b-a48a-a123dfcd2c8a
md"
### Working with larger molecules

Then, let's try it with a little larger molecules.
"

# ╔═╡ f9f50f92-d79e-42e2-a6cf-8107cd715f46
cefditoren = let
	mol = sdftomol(fetch_mol!("6437877", "Cefditoren Pivoxil", data_dir))
	remove_all_hydrogens!(mol)
	mol
end; nothing

# ╔═╡ c2ca480e-da0a-45b2-9ea2-4567d6655769
ceftazidime = let
	mol = sdftomol(fetch_mol!("5481173", "Ceftazidime", data_dir))
	remove_all_hydrogens!(mol)
	mol
end; nothing

# ╔═╡ 0689eeb0-ab08-47e4-b163-68d907eb8490
larger_mces, larger_mces_status = disconnected_mces(cefditoren, ceftazidime, timeout=10)

# ╔═╡ 268f7f7c-ae48-4b4a-898e-56f9aa893c46
md"
- As disconnected MCS takes very long time, keyword argument `timeout=10` was set to interrupt MCS calculation in 10 seconds.
- If it timed out, `MCSResult.status` will be `:timedout` and the result will be the mapping of suboptimal common substructure calculated so far.
"

# ╔═╡ fd1152c8-cbb4-4f92-aa5a-0d01d483df75
let
	edges1 = collect(keys(larger_mces))
	nodes1, vmap1 = induced_subgraph(cefditoren.graph, edges1)
	svg1 = html_fixed_size(cefditoren, 250, 250,
		atomhighlight=vmap1[vertices(nodes1)], bondhighlight=edges1)

	edges2 = collect(values(larger_mces))
	nodes2, vmap2 = induced_subgraph(ceftazidime.graph, edges2)
	svg2 = html_fixed_size(ceftazidime, 250, 250,
		atomhighlight=vmap2[vertices(nodes2)], bondhighlight=edges2)

	[svg1, svg2]
end

# ╔═╡ 1f3c9952-28bb-4e69-b84b-e6cd68ce2263
let
	@profile disconnected_mces(cefditoren, ceftazidime, timeout=10)
	Profile.print(mincount=1000)
end

# ╔═╡ 43b2240e-5c85-4b4e-8a3c-9c361b188f8d
md"
- The most costful call was `maximum_clique` which yields maximal cliques. Maximum clique detection problem is known to be NP-hard. 
- Connected MCS is far faster than disconnected MCS.
"

# ╔═╡ 22766969-41f0-44c2-974f-1650e91e4fb1
larger_conn_mces, larger_conn_mces_status = connected_mces(cefditoren, ceftazidime, timeout=10)

# ╔═╡ f0d09a83-1e9b-40bf-b83f-fc6855929f73
let
	edges1 = collect(keys(larger_conn_mces))
	nodes1, vmap1 = induced_subgraph(cefditoren.graph, edges1)
	svg1 = html_fixed_size(cefditoren, 250, 250,
		atomhighlight=vmap1[vertices(nodes1)], bondhighlight=edges1)

	edges2 = collect(values(larger_conn_mces))
	nodes2, vmap2 = induced_subgraph(ceftazidime.graph, edges2)
	svg2 = html_fixed_size(ceftazidime, 250, 250,
		atomhighlight=vmap2[vertices(nodes2)], bondhighlight=edges2)

	[svg1, svg2]
end

# ╔═╡ a2ca38e3-858e-4b7d-93f8-5662e4aeb220
md"
- Or you can use `targetsize` keyword argument to terminate the calculation with `:targetreached` status when the MCS reaches the target size. This feature is quite useful in library screening.
"

# ╔═╡ 8ac75243-2817-4df4-aad6-3cbf29dc098b
targeted_mces, targeted_mces_status = disconnected_mces(cefditoren, ceftazidime, targetsize=15)

# ╔═╡ 3a4689f2-78fe-4f87-b31c-724a903984e8
let
	edges1 = collect(keys(targeted_mces))
	nodes1, vmap1 = induced_subgraph(cefditoren.graph, edges1)
	svg1 = html_fixed_size(cefditoren, 250, 250,
		atomhighlight=vmap1[vertices(nodes1)], bondhighlight=edges1)

	edges2 = collect(values(targeted_mces))
	nodes2, vmap2 = induced_subgraph(ceftazidime.graph, edges2)
	svg2 = html_fixed_size(ceftazidime, 250, 250,
		atomhighlight=vmap2[vertices(nodes2)], bondhighlight=edges2)

	[svg1, svg2]
end

# ╔═╡ b2133510-d935-41db-aee5-162509621766
md"
### Topological constraint (known as TD-MCS)

- disconnected MCS methods can detect as many matched fragments as possible, but it does not reflect spatial relationship of each fragments.
- on the other hand, connected MCS is too strict not to allow distant matches.
- graph distance function can be used as a node attribute matcher to constrain the spatial arrangement of matched substructure fragments (topological constraint). This feature seems to be preferable in pharmacophore matching and structural similarity screening.
- topological constraint also effectively decreases the calculation cost.
- topological constraint can be used by passing keyword argument `topological=True`.
- distance mismatch tolerance parameter ``θ`` is also available as the keyword argument `tolerance`
"

# ╔═╡ 53441110-c544-403e-8bc7-dd1302470ec8
tdmces_result, tdmces_status = tdmces(cefditoren, ceftazidime, tolerance=1)

# ╔═╡ e5ddd0a1-bf60-49ad-909f-1b91cf09cc46
let
	edges1 = collect(keys(tdmces_result))
	nodes1, vmap1 = induced_subgraph(cefditoren.graph, edges1)
	svg1 = html_fixed_size(cefditoren, 250, 250,
		atomhighlight=vmap1[vertices(nodes1)], bondhighlight=edges1)

	edges2 = collect(values(tdmces_result))
	nodes2, vmap2 = induced_subgraph(ceftazidime.graph, edges2)
	svg2 = html_fixed_size(ceftazidime, 250, 250,
		atomhighlight=vmap2[vertices(nodes2)], bondhighlight=edges2)

	[svg1, svg2]
end

# ╔═╡ 00000000-0000-0000-0000-000000000001
PLUTO_PROJECT_TOML_CONTENTS = """
[deps]
Graphs = "86223c79-3864-5bf0-83f7-82e725a168b6"
MolecularGraph = "6c89ec66-9cd8-5372-9f91-fabc50dd27fd"
PlutoUI = "7f904dfe-b85e-4ff6-b463-dae2292396a8"
Profile = "9abbd945-dff8-562f-b5e8-e1ebf5ef1b79"

[compat]
Graphs = "~1.11.2"
MolecularGraph = "~0.17.1"
PlutoUI = "~0.7.62"
"""

# ╔═╡ 00000000-0000-0000-0000-000000000002
PLUTO_MANIFEST_TOML_CONTENTS = """
# This file is machine-generated - editing it directly is not advised

julia_version = "1.10.2"
manifest_format = "2.0"
project_hash = "cfa24124b25b1762460a81b2f8940a9e3f85096a"

[[deps.AbstractPlutoDingetjes]]
deps = ["Pkg"]
git-tree-sha1 = "6e1d2a35f2f90a4bc7c2ed98079b2ba09c35b83a"
uuid = "6e696c72-6542-2067-7265-42206c756150"
version = "1.3.2"

[[deps.ArgTools]]
uuid = "0dad84c5-d112-42e6-8d28-ef12dabb789f"
version = "1.1.1"

[[deps.ArnoldiMethod]]
deps = ["LinearAlgebra", "Random", "StaticArrays"]
git-tree-sha1 = "d57bd3762d308bded22c3b82d033bff85f6195c6"
uuid = "ec485272-7323-5ecc-a04f-4719b315124d"
version = "0.4.0"

[[deps.Artifacts]]
uuid = "56f22d72-fd6d-98f1-02f0-08ddc0907c33"

[[deps.Base64]]
uuid = "2a0f44e3-6c83-55bd-87e4-b1978d98bd5f"

[[deps.Bzip2_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "9e2a6b69137e6969bab0152632dcb3bc108c8bdd"
uuid = "6e34b625-4abd-537c-b88f-471c36dfa7a0"
version = "1.0.8+1"

[[deps.Cairo]]
deps = ["Cairo_jll", "Colors", "Glib_jll", "Graphics", "Libdl", "Pango_jll"]
git-tree-sha1 = "d0b3f8b4ad16cb0a2988c6788646a5e6a17b6b1b"
uuid = "159f3aea-2a34-519c-b102-8c37f9878175"
version = "1.0.5"

[[deps.Cairo_jll]]
deps = ["Artifacts", "Bzip2_jll", "CompilerSupportLibraries_jll", "Fontconfig_jll", "FreeType2_jll", "Glib_jll", "JLLWrappers", "LZO_jll", "Libdl", "Pixman_jll", "Xorg_libXext_jll", "Xorg_libXrender_jll", "Zlib_jll", "libpng_jll"]
git-tree-sha1 = "a2f1c8c668c8e3cb4cca4e57a8efdb09067bb3fd"
uuid = "83423d85-b0ee-5818-9007-b63ccbeb887a"
version = "1.18.0+2"

[[deps.ColorTypes]]
deps = ["FixedPointNumbers", "Random"]
git-tree-sha1 = "b10d0b65641d57b8b4d5e234446582de5047050d"
uuid = "3da002f7-5984-5a60-b8a6-cbb66c0b333f"
version = "0.11.5"

[[deps.Colors]]
deps = ["ColorTypes", "FixedPointNumbers", "Reexport"]
git-tree-sha1 = "362a287c3aa50601b0bc359053d5c2468f0e7ce0"
uuid = "5ae59095-9a9b-59fe-a467-6f913c188581"
version = "0.12.11"

[[deps.Compat]]
deps = ["TOML", "UUIDs"]
git-tree-sha1 = "b1c55339b7c6c350ee89f2c1604299660525b248"
uuid = "34da2185-b29b-5c13-b0c7-acf172513d20"
version = "4.15.0"
weakdeps = ["Dates", "LinearAlgebra"]

    [deps.Compat.extensions]
    CompatLinearAlgebraExt = "LinearAlgebra"

[[deps.CompilerSupportLibraries_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "e66e0078-7015-5450-92f7-15fbd957f2ae"
version = "1.1.0+0"

[[deps.ConstructionBase]]
deps = ["LinearAlgebra"]
git-tree-sha1 = "260fd2400ed2dab602a7c15cf10c1933c59930a2"
uuid = "187b0558-2788-49d3-abe0-74a17ed4e7c9"
version = "1.5.5"
weakdeps = ["IntervalSets", "StaticArrays"]

    [deps.ConstructionBase.extensions]
    ConstructionBaseIntervalSetsExt = "IntervalSets"
    ConstructionBaseStaticArraysExt = "StaticArrays"

[[deps.DataAPI]]
git-tree-sha1 = "abe83f3a2f1b857aac70ef8b269080af17764bbe"
uuid = "9a962f9c-6df0-11e9-0e5d-c546b8b5ee8a"
version = "1.16.0"

[[deps.DataStructures]]
deps = ["Compat", "InteractiveUtils", "OrderedCollections"]
git-tree-sha1 = "1d0a14036acb104d9e89698bd408f63ab58cdc82"
uuid = "864edb3b-99cc-5e75-8d2d-829cb0a9cfe8"
version = "0.18.20"

[[deps.DataValueInterfaces]]
git-tree-sha1 = "bfc1187b79289637fa0ef6d4436ebdfe6905cbd6"
uuid = "e2d170a0-9d28-54be-80f0-106bbe20a464"
version = "1.0.0"

[[deps.Dates]]
deps = ["Printf"]
uuid = "ade2ca70-3891-5945-98fb-dc099432e06a"

[[deps.DelimitedFiles]]
deps = ["Mmap"]
git-tree-sha1 = "9e2f36d3c96a820c678f2f1f1782582fcf685bae"
uuid = "8bb1440f-4735-579b-a4ab-409b98df4dab"
version = "1.9.1"

[[deps.Distributed]]
deps = ["Random", "Serialization", "Sockets"]
uuid = "8ba89e20-285c-5b6f-9357-94700520ee1b"

[[deps.Downloads]]
deps = ["ArgTools", "FileWatching", "LibCURL", "NetworkOptions"]
uuid = "f43a241f-c20a-4ad4-852c-f6b1247861c6"
version = "1.6.0"

[[deps.EarCut_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "e3290f2d49e661fbd94046d7e3726ffcb2d41053"
uuid = "5ae413db-bbd1-5e63-b57d-d24a61df00f5"
version = "2.2.4+0"

[[deps.Expat_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "1c6317308b9dc757616f0b5cb379db10494443a7"
uuid = "2e619515-83b5-522b-bb60-26c02a35a201"
version = "2.6.2+0"

[[deps.Extents]]
git-tree-sha1 = "94997910aca72897524d2237c41eb852153b0f65"
uuid = "411431e0-e8b7-467b-b5e0-f676ba4f2910"
version = "0.1.3"

[[deps.FileWatching]]
uuid = "7b1f6079-737a-58dc-b8bc-7a2ca5c1b5ee"

[[deps.FixedPointNumbers]]
deps = ["Statistics"]
git-tree-sha1 = "05882d6995ae5c12bb5f36dd2ed3f61c98cbb172"
uuid = "53c48c17-4a7d-5ca2-90c5-79b7896eea93"
version = "0.8.5"

[[deps.Fontconfig_jll]]
deps = ["Artifacts", "Bzip2_jll", "Expat_jll", "FreeType2_jll", "JLLWrappers", "Libdl", "Libuuid_jll", "Zlib_jll"]
git-tree-sha1 = "db16beca600632c95fc8aca29890d83788dd8b23"
uuid = "a3f928ae-7b40-5064-980b-68af3947d34b"
version = "2.13.96+0"

[[deps.FreeType2_jll]]
deps = ["Artifacts", "Bzip2_jll", "JLLWrappers", "Libdl", "Zlib_jll"]
git-tree-sha1 = "5c1d8ae0efc6c2e7b1fc502cbe25def8f661b7bc"
uuid = "d7e528f0-a631-5988-bf34-fe36492bcfd7"
version = "2.13.2+0"

[[deps.FriBidi_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "1ed150b39aebcc805c26b93a8d0122c940f64ce2"
uuid = "559328eb-81f9-559d-9380-de523a88c83c"
version = "1.0.14+0"

[[deps.GeoInterface]]
deps = ["Extents"]
git-tree-sha1 = "9fff8990361d5127b770e3454488360443019bb3"
uuid = "cf35fbd7-0cd7-5166-be24-54bfbe79505f"
version = "1.3.5"

[[deps.GeometryBasics]]
deps = ["EarCut_jll", "Extents", "GeoInterface", "IterTools", "LinearAlgebra", "StaticArrays", "StructArrays", "Tables"]
git-tree-sha1 = "b62f2b2d76cee0d61a2ef2b3118cd2a3215d3134"
uuid = "5c1252a2-5f33-56bf-86c9-59e7332b4326"
version = "0.4.11"

[[deps.Gettext_jll]]
deps = ["Artifacts", "CompilerSupportLibraries_jll", "JLLWrappers", "Libdl", "Libiconv_jll", "Pkg", "XML2_jll"]
git-tree-sha1 = "9b02998aba7bf074d14de89f9d37ca24a1a0b046"
uuid = "78b55507-aeef-58d4-861c-77aaff3498b1"
version = "0.21.0+0"

[[deps.Glib_jll]]
deps = ["Artifacts", "Gettext_jll", "JLLWrappers", "Libdl", "Libffi_jll", "Libiconv_jll", "Libmount_jll", "PCRE2_jll", "Zlib_jll"]
git-tree-sha1 = "7c82e6a6cd34e9d935e9aa4051b66c6ff3af59ba"
uuid = "7746bdde-850d-59dc-9ae8-88ece973131d"
version = "2.80.2+0"

[[deps.Graphics]]
deps = ["Colors", "LinearAlgebra", "NaNMath"]
git-tree-sha1 = "d61890399bc535850c4bf08e4e0d3a7ad0f21cbd"
uuid = "a2bd30eb-e257-5431-a919-1863eab51364"
version = "1.1.2"

[[deps.Graphite2_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "344bf40dcab1073aca04aa0df4fb092f920e4011"
uuid = "3b182d85-2403-5c21-9c21-1e1f0cc25472"
version = "1.3.14+0"

[[deps.Graphs]]
deps = ["ArnoldiMethod", "Compat", "DataStructures", "Distributed", "Inflate", "LinearAlgebra", "Random", "SharedArrays", "SimpleTraits", "SparseArrays", "Statistics"]
git-tree-sha1 = "ebd18c326fa6cee1efb7da9a3b45cf69da2ed4d9"
uuid = "86223c79-3864-5bf0-83f7-82e725a168b6"
version = "1.11.2"

[[deps.HarfBuzz_jll]]
deps = ["Artifacts", "Cairo_jll", "Fontconfig_jll", "FreeType2_jll", "Glib_jll", "Graphite2_jll", "JLLWrappers", "Libdl", "Libffi_jll", "Pkg"]
git-tree-sha1 = "129acf094d168394e80ee1dc4bc06ec835e510a3"
uuid = "2e76f6c2-a576-52d4-95c1-20adfe4de566"
version = "2.8.1+1"

[[deps.Hyperscript]]
deps = ["Test"]
git-tree-sha1 = "179267cfa5e712760cd43dcae385d7ea90cc25a4"
uuid = "47d2ed2b-36de-50cf-bf87-49c2cf4b8b91"
version = "0.0.5"

[[deps.HypertextLiteral]]
deps = ["Tricks"]
git-tree-sha1 = "7134810b1afce04bbc1045ca1985fbe81ce17653"
uuid = "ac1192a8-f4b3-4bfe-ba22-af5b92cd3ab2"
version = "0.9.5"

[[deps.IOCapture]]
deps = ["Logging", "Random"]
git-tree-sha1 = "b6d6bfdd7ce25b0f9b2f6b3dd56b2673a66c8770"
uuid = "b5f81e59-6552-4d32-b1f0-c071b021bf89"
version = "0.2.5"

[[deps.Inflate]]
git-tree-sha1 = "d1b1b796e47d94588b3757fe84fbf65a5ec4a80d"
uuid = "d25df0c9-e2be-5dd7-82c8-3ad0b3e990b9"
version = "0.1.5"

[[deps.InteractiveUtils]]
deps = ["Markdown"]
uuid = "b77e0a4c-d291-57a0-90e8-8db25a27a240"

[[deps.IntervalSets]]
git-tree-sha1 = "dba9ddf07f77f60450fe5d2e2beb9854d9a49bd0"
uuid = "8197267c-284f-5f27-9208-e0e47529a953"
version = "0.7.10"

    [deps.IntervalSets.extensions]
    IntervalSetsRandomExt = "Random"
    IntervalSetsRecipesBaseExt = "RecipesBase"
    IntervalSetsStatisticsExt = "Statistics"

    [deps.IntervalSets.weakdeps]
    Random = "9a3f8284-a2c9-5f02-9a11-845980a1fd5c"
    RecipesBase = "3cdcf5f2-1ef4-517c-9805-6587b60abb01"
    Statistics = "10745b16-79ce-11e8-11f9-7d13ad32a3b2"

[[deps.IterTools]]
git-tree-sha1 = "42d5f897009e7ff2cf88db414a389e5ed1bdd023"
uuid = "c8e1da08-722c-5040-9ed9-7db0dc04731e"
version = "1.10.0"

[[deps.IteratorInterfaceExtensions]]
git-tree-sha1 = "a3f24677c21f5bbe9d2a714f95dcd58337fb2856"
uuid = "82899510-4779-5014-852e-03e436cf321d"
version = "1.0.0"

[[deps.JLLWrappers]]
deps = ["Artifacts", "Preferences"]
git-tree-sha1 = "7e5d6779a1e09a36db2a7b6cff50942a0a7d0fca"
uuid = "692b3bcd-3c85-4b1f-b108-f13ce0eb3210"
version = "1.5.0"

[[deps.JSON]]
deps = ["Dates", "Mmap", "Parsers", "Unicode"]
git-tree-sha1 = "31e996f0a15c7b280ba9f76636b3ff9e2ae58c9a"
uuid = "682c06a0-de6a-54ab-a142-c8b1cf79cde6"
version = "0.21.4"

[[deps.LLVMOpenMP_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "d986ce2d884d49126836ea94ed5bfb0f12679713"
uuid = "1d63c593-3942-5779-bab2-d838dc0a180e"
version = "15.0.7+0"

[[deps.LZO_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "70c5da094887fd2cae843b8db33920bac4b6f07d"
uuid = "dd4b983a-f0e5-5f8d-a1b7-129d4a5fb1ac"
version = "2.10.2+0"

[[deps.LibCURL]]
deps = ["LibCURL_jll", "MozillaCACerts_jll"]
uuid = "b27032c2-a3e7-50c8-80cd-2d36dbcbfd21"
version = "0.6.4"

[[deps.LibCURL_jll]]
deps = ["Artifacts", "LibSSH2_jll", "Libdl", "MbedTLS_jll", "Zlib_jll", "nghttp2_jll"]
uuid = "deac9b47-8bc7-5906-a0fe-35ac56dc84c0"
version = "8.4.0+0"

[[deps.LibGit2]]
deps = ["Base64", "LibGit2_jll", "NetworkOptions", "Printf", "SHA"]
uuid = "76f85450-5226-5b5a-8eaa-529ad045b433"

[[deps.LibGit2_jll]]
deps = ["Artifacts", "LibSSH2_jll", "Libdl", "MbedTLS_jll"]
uuid = "e37daf67-58a4-590a-8e99-b0245dd2ffc5"
version = "1.6.4+0"

[[deps.LibSSH2_jll]]
deps = ["Artifacts", "Libdl", "MbedTLS_jll"]
uuid = "29816b5a-b9ab-546f-933c-edad1886dfa8"
version = "1.11.0+1"

[[deps.Libdl]]
uuid = "8f399da3-3557-5675-b5ff-fb832c97cbdb"

[[deps.Libffi_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "0b4a5d71f3e5200a7dff793393e09dfc2d874290"
uuid = "e9f186c6-92d2-5b65-8a66-fee21dc1b490"
version = "3.2.2+1"

[[deps.Libgcrypt_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Libgpg_error_jll"]
git-tree-sha1 = "9fd170c4bbfd8b935fdc5f8b7aa33532c991a673"
uuid = "d4300ac3-e22c-5743-9152-c294e39db1e4"
version = "1.8.11+0"

[[deps.Libgpg_error_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "fbb1f2bef882392312feb1ede3615ddc1e9b99ed"
uuid = "7add5ba3-2f88-524e-9cd5-f83b8a55f7b8"
version = "1.49.0+0"

[[deps.Libiconv_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "f9557a255370125b405568f9767d6d195822a175"
uuid = "94ce4f54-9a6c-5748-9c1c-f9c7231a4531"
version = "1.17.0+0"

[[deps.Libmount_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "0c4f9c4f1a50d8f35048fa0532dabbadf702f81e"
uuid = "4b2f31a3-9ecc-558c-b454-b3730dcb73e9"
version = "2.40.1+0"

[[deps.Libuuid_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "5ee6203157c120d79034c748a2acba45b82b8807"
uuid = "38a345b3-de98-5d2b-a5d3-14cd9215e700"
version = "2.40.1+0"

[[deps.LinearAlgebra]]
deps = ["Libdl", "OpenBLAS_jll", "libblastrampoline_jll"]
uuid = "37e2e46d-f89d-539d-b4ee-838fcccc9c8e"

[[deps.Logging]]
uuid = "56ddb016-857b-54e1-b83d-db4d58db5568"

[[deps.MIMEs]]
git-tree-sha1 = "c64d943587f7187e751162b3b84445bbbd79f691"
uuid = "6c6e2e6c-3030-632d-7369-2d6c69616d65"
version = "1.1.0"

[[deps.MacroTools]]
deps = ["Markdown", "Random"]
git-tree-sha1 = "2fa9ee3e63fd3a4f7a9a4f4744a52f4856de82df"
uuid = "1914dd2f-81c6-5fcd-8719-6d5c9610ff09"
version = "0.5.13"

[[deps.MakieCore]]
deps = ["ColorTypes", "GeometryBasics", "IntervalSets", "Observables"]
git-tree-sha1 = "c1c950560397ee68ad7302ee0e3efa1b07466a2f"
uuid = "20f20a25-4f0e-4fdf-b5d1-57303727442b"
version = "0.8.4"

[[deps.Markdown]]
deps = ["Base64"]
uuid = "d6f4376e-aef5-505a-96c1-9c027394607a"

[[deps.MbedTLS_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "c8ffd9c3-330d-5841-b78e-0817d7145fa1"
version = "2.28.2+1"

[[deps.Mmap]]
uuid = "a63ad114-7e13-5084-954f-fe012c677804"

[[deps.MolecularGraph]]
deps = ["Base64", "Cairo", "Colors", "Dates", "DelimitedFiles", "GeometryBasics", "Graphs", "JSON", "LinearAlgebra", "MakieCore", "Printf", "Statistics", "YAML", "coordgenlibs_jll", "libinchi_jll"]
git-tree-sha1 = "c71603f9752362e8a112f7f46ae89bb19e078069"
uuid = "6c89ec66-9cd8-5372-9f91-fabc50dd27fd"
version = "0.17.1"

[[deps.MozillaCACerts_jll]]
uuid = "14a3606d-f60d-562e-9121-12d972cd8159"
version = "2023.1.10"

[[deps.NaNMath]]
deps = ["OpenLibm_jll"]
git-tree-sha1 = "0877504529a3e5c3343c6f8b4c0381e57e4387e4"
uuid = "77ba4419-2d1f-58cd-9bb1-8ffee604a2e3"
version = "1.0.2"

[[deps.NetworkOptions]]
uuid = "ca575930-c2e3-43a9-ace4-1e988b2c1908"
version = "1.2.0"

[[deps.Observables]]
git-tree-sha1 = "7438a59546cf62428fc9d1bc94729146d37a7225"
uuid = "510215fc-4207-5dde-b226-833fc4488ee2"
version = "0.5.5"

[[deps.OpenBLAS_jll]]
deps = ["Artifacts", "CompilerSupportLibraries_jll", "Libdl"]
uuid = "4536629a-c528-5b80-bd46-f80d51c5b363"
version = "0.3.23+4"

[[deps.OpenLibm_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "05823500-19ac-5b8b-9628-191a04bc5112"
version = "0.8.1+2"

[[deps.OrderedCollections]]
git-tree-sha1 = "dfdf5519f235516220579f949664f1bf44e741c5"
uuid = "bac558e1-5e72-5ebc-8fee-abe8a469f55d"
version = "1.6.3"

[[deps.PCRE2_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "efcefdf7-47ab-520b-bdef-62a2eaa19f15"
version = "10.42.0+1"

[[deps.Pango_jll]]
deps = ["Artifacts", "Cairo_jll", "Fontconfig_jll", "FreeType2_jll", "FriBidi_jll", "Glib_jll", "HarfBuzz_jll", "JLLWrappers", "Libdl"]
git-tree-sha1 = "cb5a2ab6763464ae0f19c86c56c63d4a2b0f5bda"
uuid = "36c8627f-9965-5494-a995-c6b170f724f3"
version = "1.52.2+0"

[[deps.Parsers]]
deps = ["Dates", "PrecompileTools", "UUIDs"]
git-tree-sha1 = "8489905bcdbcfac64d1daa51ca07c0d8f0283821"
uuid = "69de0a69-1ddd-5017-9359-2bf0b02dc9f0"
version = "2.8.1"

[[deps.Pixman_jll]]
deps = ["Artifacts", "CompilerSupportLibraries_jll", "JLLWrappers", "LLVMOpenMP_jll", "Libdl"]
git-tree-sha1 = "35621f10a7531bc8fa58f74610b1bfb70a3cfc6b"
uuid = "30392449-352a-5448-841d-b1acce4e97dc"
version = "0.43.4+0"

[[deps.Pkg]]
deps = ["Artifacts", "Dates", "Downloads", "FileWatching", "LibGit2", "Libdl", "Logging", "Markdown", "Printf", "REPL", "Random", "SHA", "Serialization", "TOML", "Tar", "UUIDs", "p7zip_jll"]
uuid = "44cfe95a-1eb2-52ea-b672-e2afdf69b78f"
version = "1.10.0"

[[deps.PlutoUI]]
deps = ["AbstractPlutoDingetjes", "Base64", "ColorTypes", "Dates", "FixedPointNumbers", "Hyperscript", "HypertextLiteral", "IOCapture", "InteractiveUtils", "JSON", "Logging", "MIMEs", "Markdown", "Random", "Reexport", "URIs", "UUIDs"]
git-tree-sha1 = "d3de2694b52a01ce61a036f18ea9c0f61c4a9230"
uuid = "7f904dfe-b85e-4ff6-b463-dae2292396a8"
version = "0.7.62"

[[deps.PrecompileTools]]
deps = ["Preferences"]
git-tree-sha1 = "5aa36f7049a63a1528fe8f7c3f2113413ffd4e1f"
uuid = "aea7be01-6a6a-4083-8856-8a6e6704d82a"
version = "1.2.1"

[[deps.Preferences]]
deps = ["TOML"]
git-tree-sha1 = "9306f6085165d270f7e3db02af26a400d580f5c6"
uuid = "21216c6a-2e73-6563-6e65-726566657250"
version = "1.4.3"

[[deps.Printf]]
deps = ["Unicode"]
uuid = "de0858da-6303-5e67-8744-51eddeeeb8d7"

[[deps.Profile]]
deps = ["Printf"]
uuid = "9abbd945-dff8-562f-b5e8-e1ebf5ef1b79"

[[deps.REPL]]
deps = ["InteractiveUtils", "Markdown", "Sockets", "Unicode"]
uuid = "3fa0cd96-eef1-5676-8a61-b3b8758bbffb"

[[deps.Random]]
deps = ["SHA"]
uuid = "9a3f8284-a2c9-5f02-9a11-845980a1fd5c"

[[deps.Reexport]]
git-tree-sha1 = "45e428421666073eab6f2da5c9d310d99bb12f9b"
uuid = "189a3867-3050-52da-a836-e630ba90ab69"
version = "1.2.2"

[[deps.SHA]]
uuid = "ea8e919c-243c-51af-8825-aaa63cd721ce"
version = "0.7.0"

[[deps.Serialization]]
uuid = "9e88b42a-f829-5b0c-bbe9-9e923198166b"

[[deps.SharedArrays]]
deps = ["Distributed", "Mmap", "Random", "Serialization"]
uuid = "1a1011a3-84de-559e-8e89-a11a2f7dc383"

[[deps.SimpleTraits]]
deps = ["InteractiveUtils", "MacroTools"]
git-tree-sha1 = "5d7e3f4e11935503d3ecaf7186eac40602e7d231"
uuid = "699a6c99-e7fa-54fc-8d76-47d257e15c1d"
version = "0.9.4"

[[deps.Sockets]]
uuid = "6462fe0b-24de-5631-8697-dd941f90decc"

[[deps.SparseArrays]]
deps = ["Libdl", "LinearAlgebra", "Random", "Serialization", "SuiteSparse_jll"]
uuid = "2f01184e-e22b-5df5-ae63-d93ebab69eaf"
version = "1.10.0"

[[deps.StaticArrays]]
deps = ["LinearAlgebra", "PrecompileTools", "Random", "StaticArraysCore"]
git-tree-sha1 = "eeafab08ae20c62c44c8399ccb9354a04b80db50"
uuid = "90137ffa-7385-5640-81b9-e52037218182"
version = "1.9.7"

    [deps.StaticArrays.extensions]
    StaticArraysChainRulesCoreExt = "ChainRulesCore"
    StaticArraysStatisticsExt = "Statistics"

    [deps.StaticArrays.weakdeps]
    ChainRulesCore = "d360d2e6-b24c-11e9-a2a3-2a2ae2dbcce4"
    Statistics = "10745b16-79ce-11e8-11f9-7d13ad32a3b2"

[[deps.StaticArraysCore]]
git-tree-sha1 = "192954ef1208c7019899fbf8049e717f92959682"
uuid = "1e83bf80-4336-4d27-bf5d-d5a4f845583c"
version = "1.4.3"

[[deps.Statistics]]
deps = ["LinearAlgebra"]
git-tree-sha1 = "ae3bb1eb3bba077cd276bc5cfc337cc65c3075c0"
uuid = "10745b16-79ce-11e8-11f9-7d13ad32a3b2"
version = "1.10.0"
weakdeps = ["SparseArrays"]

    [deps.Statistics.extensions]
    SparseArraysExt = ["SparseArrays"]

[[deps.StringEncodings]]
deps = ["Libiconv_jll"]
git-tree-sha1 = "b765e46ba27ecf6b44faf70df40c57aa3a547dcb"
uuid = "69024149-9ee7-55f6-a4c4-859efe599b68"
version = "0.3.7"

[[deps.StructArrays]]
deps = ["ConstructionBase", "DataAPI", "Tables"]
git-tree-sha1 = "f4dc295e983502292c4c3f951dbb4e985e35b3be"
uuid = "09ab397b-f2b6-538f-b94a-2f83cf4a842a"
version = "0.6.18"

    [deps.StructArrays.extensions]
    StructArraysAdaptExt = "Adapt"
    StructArraysGPUArraysCoreExt = "GPUArraysCore"
    StructArraysSparseArraysExt = "SparseArrays"
    StructArraysStaticArraysExt = "StaticArrays"

    [deps.StructArrays.weakdeps]
    Adapt = "79e6a3ab-5dfb-504d-930d-738a2a938a0e"
    GPUArraysCore = "46192b85-c4d5-4398-a991-12ede77f4527"
    SparseArrays = "2f01184e-e22b-5df5-ae63-d93ebab69eaf"
    StaticArrays = "90137ffa-7385-5640-81b9-e52037218182"

[[deps.SuiteSparse_jll]]
deps = ["Artifacts", "Libdl", "libblastrampoline_jll"]
uuid = "bea87d4a-7f5b-5778-9afe-8cc45184846c"
version = "7.2.1+1"

[[deps.TOML]]
deps = ["Dates"]
uuid = "fa267f1f-6049-4f14-aa54-33bafae1ed76"
version = "1.0.3"

[[deps.TableTraits]]
deps = ["IteratorInterfaceExtensions"]
git-tree-sha1 = "c06b2f539df1c6efa794486abfb6ed2022561a39"
uuid = "3783bdb8-4a98-5b6b-af9a-565f29a5fe9c"
version = "1.0.1"

[[deps.Tables]]
deps = ["DataAPI", "DataValueInterfaces", "IteratorInterfaceExtensions", "OrderedCollections", "TableTraits"]
git-tree-sha1 = "598cd7c1f68d1e205689b1c2fe65a9f85846f297"
uuid = "bd369af6-aec1-5ad0-b16a-f7cc5008161c"
version = "1.12.0"

[[deps.Tar]]
deps = ["ArgTools", "SHA"]
uuid = "a4e569a6-e804-4fa4-b0f3-eef7a1d5b13e"
version = "1.10.0"

[[deps.Test]]
deps = ["InteractiveUtils", "Logging", "Random", "Serialization"]
uuid = "8dfed614-e22c-5e08-85e1-65c5234f0b40"

[[deps.Tricks]]
git-tree-sha1 = "6cae795a5a9313bbb4f60683f7263318fc7d1505"
uuid = "410a4b4d-49e4-4fbc-ab6d-cb71b17b3775"
version = "0.1.10"

[[deps.URIs]]
git-tree-sha1 = "cbbebadbcc76c5ca1cc4b4f3b0614b3e603b5000"
uuid = "5c2747f8-b7ea-4ff2-ba2e-563bfd36b1d4"
version = "1.5.2"

[[deps.UUIDs]]
deps = ["Random", "SHA"]
uuid = "cf7118a7-6976-5b1a-9a39-7adc72f591a4"

[[deps.Unicode]]
uuid = "4ec0a83e-493e-50e2-b9ac-8f72acf5a8f5"

[[deps.XML2_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Libiconv_jll", "Zlib_jll"]
git-tree-sha1 = "d9717ce3518dc68a99e6b96300813760d887a01d"
uuid = "02c8fc9c-b97f-50b9-bbe4-9be30ff0a78a"
version = "2.13.1+0"

[[deps.XSLT_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Libgcrypt_jll", "Libgpg_error_jll", "Libiconv_jll", "XML2_jll", "Zlib_jll"]
git-tree-sha1 = "a54ee957f4c86b526460a720dbc882fa5edcbefc"
uuid = "aed1982a-8fda-507f-9586-7b0439959a61"
version = "1.1.41+0"

[[deps.Xorg_libX11_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Xorg_libxcb_jll", "Xorg_xtrans_jll"]
git-tree-sha1 = "afead5aba5aa507ad5a3bf01f58f82c8d1403495"
uuid = "4f6342f7-b3d2-589e-9d20-edeb45f2b2bc"
version = "1.8.6+0"

[[deps.Xorg_libXau_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "6035850dcc70518ca32f012e46015b9beeda49d8"
uuid = "0c0b7dd1-d40b-584c-a123-a41640f87eec"
version = "1.0.11+0"

[[deps.Xorg_libXdmcp_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "34d526d318358a859d7de23da945578e8e8727b7"
uuid = "a3789734-cfe1-5b06-b2d0-1dd0d9d62d05"
version = "1.1.4+0"

[[deps.Xorg_libXext_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Xorg_libX11_jll"]
git-tree-sha1 = "d2d1a5c49fae4ba39983f63de6afcbea47194e85"
uuid = "1082639a-0dae-5f34-9b06-72781eeb8cb3"
version = "1.3.6+0"

[[deps.Xorg_libXrender_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Xorg_libX11_jll"]
git-tree-sha1 = "47e45cd78224c53109495b3e324df0c37bb61fbe"
uuid = "ea2f1a96-1ddc-540d-b46f-429655e07cfa"
version = "0.9.11+0"

[[deps.Xorg_libpthread_stubs_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "8fdda4c692503d44d04a0603d9ac0982054635f9"
uuid = "14d82f49-176c-5ed1-bb49-ad3f5cbd8c74"
version = "0.1.1+0"

[[deps.Xorg_libxcb_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "XSLT_jll", "Xorg_libXau_jll", "Xorg_libXdmcp_jll", "Xorg_libpthread_stubs_jll"]
git-tree-sha1 = "bcd466676fef0878338c61e655629fa7bbc69d8e"
uuid = "c7cfdc94-dc32-55de-ac96-5a1b8d977c5b"
version = "1.17.0+0"

[[deps.Xorg_xtrans_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "e92a1a012a10506618f10b7047e478403a046c77"
uuid = "c5fb5394-a638-5e4d-96e5-b29de1b5cf10"
version = "1.5.0+0"

[[deps.YAML]]
deps = ["Base64", "Dates", "Printf", "StringEncodings"]
git-tree-sha1 = "80c3218f29cbc47111ac87e7be5e69cc05c6dd36"
uuid = "ddb6d928-2868-570f-bddf-ab3f9cf99eb6"
version = "0.4.11"

[[deps.Zlib_jll]]
deps = ["Libdl"]
uuid = "83775a58-1f1d-513f-b197-d71354ab007a"
version = "1.2.13+1"

[[deps.coordgenlibs_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "93fce743c1b36cde0efde11b1867cb7d16b13bf8"
uuid = "f6050b86-aaaf-512f-8549-0afff1b4d57f"
version = "3.0.2+0"

[[deps.libblastrampoline_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "8e850b90-86db-534c-a0d3-1478176c7d93"
version = "5.8.0+1"

[[deps.libinchi_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "e81a593eb6a1a57d4262a3ed18a6efbc5d8ba83c"
uuid = "172afb32-8f1c-513b-968f-184fcd77af72"
version = "1.6.0+0"

[[deps.libpng_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Zlib_jll"]
git-tree-sha1 = "d7015d2e18a5fd9a4f47de711837e980519781a4"
uuid = "b53b4c65-9356-5827-b1ea-8c7a1a84506f"
version = "1.6.43+1"

[[deps.nghttp2_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "8e850ede-7688-5339-a07c-302acd2aaf8d"
version = "1.52.0+1"

[[deps.p7zip_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "3f19e933-33d8-53b3-aaab-bd5110c3b7a0"
version = "17.4.0+2"
"""

# ╔═╡ Cell order:
# ╟─c324c158-d7fa-11ed-0300-93b6975d9deb
# ╠═8b4b7b1a-8f77-4917-b55c-3f32ddd3bb4f
# ╠═62d3c057-1c65-44fd-ac25-266bdb26e536
# ╠═29a84294-8ab8-4d93-9d05-adcf67f6c57d
# ╟─65b40864-4cbc-4122-9b58-cfbecdee34ee
# ╠═18e3d457-bd9e-418f-a08e-25eefcd02cd0
# ╠═0c2ddc86-71ac-43d1-ae86-71510b216d92
# ╠═8b645955-b2ce-4b2a-9793-18a1612e2a75
# ╠═7b38cdb4-7afd-4957-b6d3-116b4bd90d96
# ╟─154d878f-230d-4e1a-a8b1-f261e226594a
# ╠═8ac8565c-1f9e-42e7-a90d-705971864955
# ╠═0fbaefff-78f8-4b27-aaf4-b951fe975df2
# ╟─3c7be77e-6116-4c93-b3c0-a058cdd20a52
# ╠═0fb4d717-6422-4e1b-a345-a5841d164d9f
# ╠═a0ae8cb9-a5b7-4e8d-834b-3bea0bbcc9de
# ╠═8b4b896d-f6e7-427c-84f5-0bcc44eb5fc9
# ╠═2cdd67cb-35d0-4bab-b8b9-5ce37552398e
# ╟─b7a007c9-8b18-428b-a48a-a123dfcd2c8a
# ╠═f9f50f92-d79e-42e2-a6cf-8107cd715f46
# ╠═c2ca480e-da0a-45b2-9ea2-4567d6655769
# ╠═0689eeb0-ab08-47e4-b163-68d907eb8490
# ╟─268f7f7c-ae48-4b4a-898e-56f9aa893c46
# ╠═fd1152c8-cbb4-4f92-aa5a-0d01d483df75
# ╠═1f3c9952-28bb-4e69-b84b-e6cd68ce2263
# ╠═43b2240e-5c85-4b4e-8a3c-9c361b188f8d
# ╠═22766969-41f0-44c2-974f-1650e91e4fb1
# ╠═8ed41278-460b-490c-b691-232418a53a65
# ╠═f0d09a83-1e9b-40bf-b83f-fc6855929f73
# ╟─a2ca38e3-858e-4b7d-93f8-5662e4aeb220
# ╠═8ac75243-2817-4df4-aad6-3cbf29dc098b
# ╠═3a4689f2-78fe-4f87-b31c-724a903984e8
# ╟─b2133510-d935-41db-aee5-162509621766
# ╠═53441110-c544-403e-8bc7-dd1302470ec8
# ╠═e5ddd0a1-bf60-49ad-909f-1b91cf09cc46
# ╟─00000000-0000-0000-0000-000000000001
# ╟─00000000-0000-0000-0000-000000000002
