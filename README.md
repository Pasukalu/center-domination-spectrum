# Distances between central vertices in graphs with small total domination number

[Read the manuscript](paper/main.pdf) · [LaTeX source](paper/main.tex) · [Selection and priority audit](research/selection-and-priority.md) · [Proof review](verification/proof-review.md) · [Research checks](https://github.com/Pasukalu/center-domination-spectrum/actions/workflows/research.yml)

Let *C* be the vertices of minimum eccentricity in a finite connected simple graph, and let `mean(C)` average their ambient distances over distinct unordered pairs. The manuscript uses zero for a singleton center. A dominating edge is an edge whose endpoints together supply a neighbor to every vertex.

| Question | Result |
| --- | --- |
| Written on the Wall II, no. 268 | The strict mean inequality follows by averaging the spanning-tree bound from the proof of Lemma 3, equation (5), and the equality-case argument from the proof of Theorem 5 of DeLaViña et al. (2007). The paper gives the deduction and an alternative construction of the tree. |
| Which graphs occur as an induced center when the total domination number is two? | A finite graph with at least two vertices occurs exactly when it contains a dominating edge. Every specified dominating edge is preserved in an explicit realization with four additional vertices, radius two and diameter three. |
| When are four added vertices necessary? | If both ends of the specified dominating edge have pendant neighbors, exactly four vertices are necessary. For every double star with both sides nonempty, the unconstrained minimum is two and the edge-preserving minimum is four. |
| Which means occur for exactly *m* central vertices and total domination number two? | For *m* ≥ 2, set *M* = binom(*m*, 2). The attainable values are 2 − *j*/*M* for every integer *j* from *m* − 1 through *M*. The sharp maximum is 2 − 2/*m*. Every value has a realization with only two noncentral vertices. |
| Written on the Wall II, no. 269 | The ceiling inequality holds for odd total domination number and in the four-cycle-free case of total domination number two. Even values of at least four remain open here. |

The catalogue search and follow-up priority audit cover eight sources. The 2007 spanning-tree bound and the classical unconstrained center extension are prior work. The four-vertex lower bound also follows from a short marked-edge adaptation of Chen's leaf restriction and Behrens' identification argument. Priority for the exact spectrum and the specified-edge results remains unconfirmed. The manuscript is an AI-generated research preprint.

## Formal coverage

`CenterRealization.lean` proves both directions of the induced-center characterization and the radius and diameter of the construction. `CenterObstruction.lean` proves the sharp four-vertex bound and the two-vertex lower bound for every proper center. `CenterDomination.lean` gives the bridge to Mathlib shortest-path distances. `CenterCounts.lean` proves the pair-sum identity, the singleton convention, and no. 268 for every graph having a dominating edge. `CenterFan.lean` verifies the centers, domination and distances in the spectrum construction. The full integer spectrum and tree equality criterion, the general spanning-tree argument for no. 268, and the ceiling corollary have paper proofs.

The [historical web session](verification/lean-web.txt) checked 18 declarations in the original version. The current CI audit runs `lake build`, prints the axiom closures of the named declarations and runs `lake env leanchecker --fresh CenterObstruction` on the complete import chain. Each commit has its own [research checks](https://github.com/Pasukalu/center-domination-spectrum/actions/workflows/research.yml).

## Reproduce

With Elan, Python 3.10 or newer, and an internet connection for the pinned Mathlib cache, run these commands from the repository root.

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Metric Mathlib.Tactic.DeriveFintype Mathlib.Algebra.Order.Field.Rat Mathlib.Algebra.Order.BigOperators.Group.Finset
python3 scripts/verify_lean.py
python3 experiments/enumerate_graphs.py --out reproduced.json
python3 -c "import json; assert json.load(open('reproduced.json')) == json.load(open('experiments/results.json'))"
python3 experiments/independent_check.py
python3 experiments/check_appendages.py
python3 experiments/audit_seven.py
```

The first enumerator uses integers and rational numbers. It checks 27,475 connected labelled graphs on two through six vertices, plus 240 seeded larger graphs, 833 instances of the spectrum construction and 238 specified-edge extensions. The independent checker computes distances with Floyd–Warshall and enumerates spanning trees using Prüfer words on up to five vertices. A third script examines all 32,768 labelled extensions of the four-vertex path by three vertices. Twelve have the required center and none preserves its dominating edge. With two new vertices, exactly two of the 512 labelled extensions have the required center and neither preserves the edge.

The independent seven-vertex audit uses only the Python standard library. It groups all labelled graphs into permutation orbits, compares every total dominating set against the minimum spanning-tree diameter, and checks the center distances by integer arithmetic. At order seven it covers 853 connected isomorphism classes representing 1,866,256 labelled graphs.

Compile the manuscript with TeX Live's `pdflatex`, the Latin Modern fonts and the packages declared in its preamble.

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

For the candidate-by-candidate record, the seven score columns and the five preliminary explorations, see [the 41-row table](research/candidates.csv) and [research notes](research/selection-and-priority.md). See [LICENSE](LICENSE) for the terms of reuse.

