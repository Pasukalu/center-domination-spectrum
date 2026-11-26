# Proof review

## Correspondence of statements

The manuscript uses finite connected loopless undirected graphs. Distances are measured in the ambient graph even when the induced center admits longer paths. For a finite connected graph the eccentricity of a vertex is the least radius of a closed ball at that vertex containing the graph. Thus a vertex has minimum eccentricity exactly when it covers the graph at every radius at which any vertex does. This is `Central`; `central_iff_metric` and `within_iff_dist` identify the graph metric with Mathlib's `SimpleGraph.dist`.

| Manuscript | Formal declaration or remaining step |
| --- | --- |
| Theorem 3.2, both directions for graphs of order at least two | `realization_iff` requires two distinct vertices. Its witness includes a finite ambient type, connectedness, a dominating edge, an injective map reflecting and preserving adjacency, and image equal to the whole center. |
| Theorem 3.2, specified edge and four extra vertices | `Ext.realizes_center` preserves that very edge. The ambient type `Ext V` has one old constructor with argument in V and four nullary constructors. `extension_radius_and_diameter` proves the two upper bounds and the two witnesses excluding a smaller value. |
| Theorem 3.1, distances and construction | `center_distance_sum` counts oriented distinct pairs. Every unordered pair has two orientations. `Fan.centers`, `Fan.pair_dominates`, `Fan.spoke_distance` and `Fan.hub_distance` verify the parametrized construction for arbitrary added spoke edges. The all-integer spectrum, minimum order and edge-cardinality estimates are proved in the manuscript. |
| Theorem 2.2 (no. 268) | `Claim268` is the assigned statement. `strict_mean_of_close_pair` proves the analytic final step. Lemma 2.1 and its geometric consequences have a paper proof. |
| Corollary 4.1 (no. 269) and the common bound for 259–261 | Paper or research-note proofs. |

## Cross-checks of the arguments

1. **Connected spine.** Each assigned part contains a connected component of the selected set plus vertices adjacent directly to that component. When a crossing edge has both ends outside the selected set, retaining both ends connects the two components. A tree of such crossings needs at most two additional vertices per crossing, including when the same endpoint is reused. A tree path can meet attached leaves only at its ends. This gives the stated diameter, also for a selected edge alone.
2. **Strictness at equality.** If the graph radius equals the size k of a minimum total dominating set, every spanning tree has radius at least k. The spine tree has diameter at most 2k−1. Its diameter is consequently 2k−1 and both midpoints retain eccentricity k in the graph. Their distance one supplies a strict summand because k≥2. The singleton-center convention agrees with Lean's zero quotient for an empty pair set.
3. **Independent distance check for the extension.** The open neighborhoods of A and B are {v,Q} and {u,P}, respectively. P is adjacent to neither v nor Q, and Q to neither u nor P. Hence d(P,A) and d(Q,B) exceed two. The original edge dominates, so all distances are at most three. For two old nonadjacent vertices at least one of P,Q is a common neighbor. An old vertex reaches A via Q unless it is u, in which case it uses v. It reaches B by the symmetric argument. Thus the center has neither missing nor extra vertices. K₂ gives a valid smallest input. The one-vertex domain would fail necessity and is excluded explicitly.
4. **Counting and attainability.** For an m-vertex center first count actual edges, each contributing one, then its nonedges, each contributing two. The distance sum decreases by exactly one for each added spoke edge, including the last possible one. The two outside vertices always remain at distance three. At m=2 the allowed list has a single value and the construction is the path on four vertices. If the center is proper, any diameter pair supplies two distinct outside vertices.
5. **Four-cycle convention.** The forbidden configuration includes cycles with a chord. This rules out a crossing edge between the two exclusive neighbor sets, an edge from a common neighbor to either exclusive set, and two distinct common neighbors. These exclusions force distance three across the two exclusive sets. When there is a universal vertex, central vertices are exactly the universal vertices. No assertion for all even domination numbers is inferred.
6. **Implementation independence.** The second finite checker uses a distance matrix and all Prüfer words of the relevant order. It enumerates tree leaves explicitly. The principal enumerator instead uses mask neighborhoods, breadth-first layers and connected dominating sets to optimize the leaf count. Neither computation supplies any logical premise in the proofs.

These are separate derivations and executable checks within an AI-generated project. They have not undergone external human peer review.

