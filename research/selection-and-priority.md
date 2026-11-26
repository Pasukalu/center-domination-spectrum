# Research selection and priority record

Search date: 26 November 2026. The main catalogue had a 19 November revision.
A 6 November printout is useful for definitions, but it predates the live list.

## Selection

The 41 rows in `candidates.csv` carry seven separate scores from 1 (poor) to 5
(strong), in the requested order. The sum is unweighted. Scores measure
research suitability and represent judgments, not probabilities. A historical
benchmark question, a lack of issue hits or an open flag alone does not
establish that a problem is unsolved.

The live Graffiti.pc filters displayed 526 entries and 165 open on this visit.
Of 35 graph entries sampled from the live open labels, four were removed for
competing work found by searching the primary GitHub tracker. This left 31
catalogue-labelled candidates. Three OEIS rows and one MathOverflow row are
additional leads whose open status needs corroboration. Two Erdős problems
were included as controls for recognizing already settled questions. All 41
rows have scores, including exclusions. Among the retained candidates the
leading five were 268 (34), 269 (33), 261 (32), 259 (31), and 260 (30).

## Sources actually consulted

| Resource | Material and decision |
| --- | --- |
| Google DeepMind Formal Conjectures | Consulted the repository, the WrittenOnTheWallII index, the graph vertex-distance definitions, and the primary issue tracker. Filename checks for GraphConjecture268.lean and GraphConjecture269.lean both returned 404. A directory index of 63 research/textbook files contained no entry for 268. Used the catalogue statement and the same distinct-pair averaging convention. [Code](https://github.com/google-deepmind/formal-conjectures), [distance definitions](https://google-deepmind.github.io/formal-conjectures/src/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance/), [index](https://trough.jackmccarthy.org/roadmap/formal-conjectures/written-on-the-wall-ii/index.html) |
| Erdős Problems | Inspected the primary database and the source formalizations for 1 and 2. Both have a disproof recorded. The covering-system question already had Hough's 2015 answer. [Status data](https://github.com/teorth/erdosproblems/blob/main/data/problems.yaml), [problem 1](https://www.erdosproblems.com/1), [problem 2](https://www.erdosproblems.com/2) |
| OEIS Open | Read Adamczewski's 492-problem benchmark description and compared metadata for A055487, A070823 and A096535 to the current entries. A historical conjecture field does not settle priority. [Paper](https://arxiv.org/abs/2608.11941), [A055487](https://oeis.org/A055487), [A070823](https://oeis.org/A070823), [A096535](https://oeis.org/A096535) |
| MathOverflow | Checked the domination tag and question 474765. The posted answer addresses the tree case, illustrating why an answer-count filter cannot identify solved questions reliably. A targeted search on center distance and dominating edges produced no exact-priority match. [Discussion](https://mathoverflow.net/q/474765), [tag](https://mathoverflow.net/questions/tagged/graph-domination) |
| arXiv | Searched graph centers, distance spectra, specified dominating edges, total domination and Graffiti conjectures. The proof paper on 141--143 and the OEIS papers provide exclusion checks for rapidly moving lists. [141--143](https://arxiv.org/abs/2608.01396), [further OEIS proofs](https://arxiv.org/abs/2607.24832), [center/periphery appendages](https://arxiv.org/abs/1705.07982) |
| OpenAI Math | Examined the catalogue, its 24 November change log and a targeted repository search for Graffiti.pc and 268. No exact result surfaced. Individual manuscripts and their formalizations have different verification status. [Catalogue](https://github.com/openai/math), [changes](https://github.com/openai/math/blob/main/history.md) |
| LeanOpenProblems-results | Consulted the run inventory, criterion for a passing sample and the OEIS provenance file. The benchmark is sequence/Erdős-focused. No proof of the graph theorem can be inferred from these scores. The three sequence reserves were not promoted on the basis of incomplete run matching. [Results](https://github.com/epoch-research/LeanOpenProblems-results), [metadata](https://github.com/epoch-research/LeanOpenProblems-results/tree/main/metadata/oeis) |
| Written on the Wall II | Read the author's current interactive entries for the five finalists, the 6 November printout, and its distinct-pair definition under 241--243. Both 268 and 269 showed open in the live catalogue visited. The C4-free condition is exclusion as an ordinary subgraph. [Current catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html), [printout](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf), [C4 convention](https://github.com/google-deepmind/formal-conjectures/issues/4423) |

## Cross-checks and exclusions

For each of the 35 graph numbers the repository issue search used
`repo:google-deepmind/formal-conjectures NUMBER in:title`, screening the
returned titles for Graffiti, WOWII and Written on the Wall. This method can
miss multi-number posts and titles without these words. Broader web queries
covered the short list, names of invariants, close graph families and papers.
The four docket hits include a competing proof claim for 144, a treatment of
the complement invariant for 161 and explicit counterexample reports for 252
and 253. These entries were conservatively excluded without endorsing
every assertion of the submitters. See the four individual links in the CSV.
Other examples filtered out before scoring included 141--143, 198a, 200,
233 and 262. The catalogue reports a tree counterexample to 262. Henning
and Yeo published a stronger lower bound settling 233.
[Henning and Yeo](https://pure.uj.ac.za/en/publications/a-new-lower-bound-for-the-total-domination-number-in-graphs-provi/).

## Five preliminary explorations

1. **268.** Integer cross-multiplication of the mean inequality and a rational
   calculation both support a strict upper bound on the mean. Small examples
   include equality of radius and total domination. A spanning tree of diameter
   at most 2k-1 supplies two adjacent central vertices exactly where the
   elementary radius bound loses strictness. The extremizers at k=2 led to
   the full spectrum and the center-realization theorem.
2. **269.** The stronger ceiling does not extend to all graphs. A center of
   size three in the extremal family has mean 4/3 and k=2. With four-cycles
   prohibited, a dominating edge instead has a clique as center. An odd
   minimum total dominating set gives a shorter spanning-tree diameter
   regardless of four-cycles. The even cases k≥4 remain unresolved here.
3. **261.** Cross-multiplied the conjecture and identified the potentially
   difficult maximum-leaf value 3. For paths and cycles the outside boundary
   of the degree-two set has size at most two. The lemma below covers L≥4.
4. **259.** The same large-leaf result applies to the outside boundary of
   the maximum-degree set. On a path this boundary contains at most its two
   endpoints, and on a cycle it is empty. The low-leaf branch is not decided
   by the spanning-tree bound alone.
5. **260.** For any tree, peripheral vertices are leaves when the order is
   at least three. Their outside boundary has at most as many vertices as
   there are leaves, so kL≥2 times its size. For general graphs the same
   large-leaf argument applies. Low-leaf cyclic graphs remain to analyze.

### Common partial bound for 259--261

Let G be connected and let L≥4 be the maximum number of leaves of a spanning
tree. For every subset S one has 2|N(S) minus S|≤kL for k=γ_t.
A vertex of degree Δ gives a star on Δ leaves, which can be extended to a
spanning tree without decreasing its leaf count (add one outside vertex by
one edge at a time). Thus Δ≤L. The empty and singleton S cases follow.
For |S|≥2 the boundary has at most n-2 vertices. The proof of Lemma 2.1 in
the paper constructs a connected dominating set K of size at most 2k-2.
Attaching the other vertices as leaves gives n≤L+2k-2. Therefore
2(n-2)≤2L+4k-8≤kL by (k-2)(L-4)≥0. This is a proof for all graphs in the
stated class; the small-graph experiments were exploratory only.

## Post-proof priority audit

Repeated searches after the constructions were known used the problem number
and *average distance between center vertices*, *total domination*, *dominating
edge*, *prescribed induced center*, *diameter three*, *center appendage
number*, *Wiener index on the center*, and *center distance spectrum*, in
English and with center/centre and DeLaViña/DeLaVina variants. Direct
comparisons are as follows.

| Result in this work | Closest earlier result | Priority interpretation |
| --- | --- | --- |
| Radius ≤ total domination | DeLaViña, Liu, Pepper, Waller and West, 2007, Theorem 3 | Known. Their Theorem 5 proof also uses the promotion of adjacent tree centers to graph centers. |
| Strict center mean and no. 268 | Equation (5) in the proof of Lemma 3 of DeLaViña et al. (2007) gives the component-sensitive spanning-tree bound used for a minimum total dominating set. Their proof of Theorem 5 gives the adjacent-center step. | The mean inequality follows directly by averaging. Its catalogue entry still says open. The entry does not settle priority. |
| Full center-mean spectrum for k=2 and fixed m | Ambient total distance / fixed radius work optimizes a different vertex-pair sum. Fedoryaeva studies typical central vertex counts at fixed diameter. | Candidate original extremal theorem. Sharpness and identical order for every value are proved explicitly in the paper. |
| Prescribed induced center with a specified dominating edge | Buckley, Miller and Slater (1981) give the unconstrained four-vertex bound. Guest et al. (2021), Proposition 2.1 and Figure 2, realize every center at radius two and diameter three by replacing one central vertex of a seven-vertex graph. | The comparison concerns preservation of the specified edge together with the four-vertex bound. Priority for that combination is unconfirmed. [Guest et al., pp. 1482–1483](https://arxiv.org/abs/2111.00415) |
| Four-vertex lower bound with opposite pendant neighbors | Buckley, Miller and Slater classify ordinary tree appendage numbers. Behrens, Ch. 2, surveys constraints on neighbors of peripheral vertices and the algorithmic centralizing-number literature. In particular, the unconstrained double-star value two is already known. | Preserving the specified dominating edge forces four even for these double stars. We found no exact statement of this constrained gap. The lower-bound proof covers nontrees as well. |
| No. 269 for odd k or for k=2 without a four-cycle | Radius estimates and the elementary structure of a four-cycle-free graph around a dominating edge | Partial result only. No claim to resolve no. 269 in general. |

A second search after deriving the obstruction included “centralizing number”, “centralizer”, “central appendage”, “almost self-centered”, “double star”, “pendant neighbor”, “dominating edge” and “diameter three”. Behrens' Lemma 2.1.3 records prior peripheral-neighborhood restrictions, including one for a leaf. Her Lemma 2.1.4 addresses radius-two centralizers with three outside vertices. These results concern the unmarked optimization. [Behrens, institutional copy](https://digitalcommons.unl.edu/mathstudent/63/).

The original articles and the catalogue outweigh search snippets. An exact
match could still appear under terminology not indexed by the searches, in
a dissertation or in an unpublished note. No human referee, journal decision,
catalogue update or priority certification has been obtained.
[2007 article](https://www.uhd.edu/documents/academics/sciences/total-dom-2007.pdf),
[1981 article](https://doi.org/10.1002/jgt.3190050413),
[Fedoryaeva](https://www.mathnet.ru/eng/semr1377),
[fixed-radius total distance](https://doi.org/10.1002/jgt.22644).

