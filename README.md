# Distances between central vertices in graphs with small total domination number

> **Phase II audit: not release-ready.** See [independent audit](verification/phase2-independent-audit-2026-11-26.md) for confirmed prior work, independent checks, and formalization limitations. The general spanning-tree argument and full spectrum/ceiling results are not yet fully machine-checked.

[Previous compiled manuscript](paper/main.pdf) (may predate the new theorem) · [LaTeX source](paper/main.tex) · [Selection and priority audit](research/selection-and-priority.md) · [Proof review](verification/proof-review.md) · [Research checks](https://github.com/Pasukalu/center-domination-spectrum/actions/workflows/research.yml)

Let *C* be the vertices of minimum eccentricity in a finite connected simple graph, and let `mean(C)` average their ambient distances over distinct unordered pairs. The manuscript uses zero for a singleton center. A dominating edge is an edge whose endpoints together supply a neighbor to every vertex.

| Question | Result |
| --- | --- |
| Written on the Wall II, no. 268 | The mean is strictly smaller than the minimum size of a total dominating set. This gives the proposed floor inequality. The paper gives a spanning-tree proof. |
| Which graphs occur as an induced center when the total domination number is two? | A finite graph with at least two vertices occurs exactly when it contains a dominating edge. Every specified dominating edge is preserved in an explicit realization with four additional vertices, radius two and diameter three. |
| When are four added vertices necessary? | If both ends of the specified dominating edge have pendant neighbors, exactly four vertices are necessary. For every double star with both sides nonempty, the unconstrained minimum is two and the edge-preserving minimum is four. |
| What is the minimum number of added vertices with a fixed dominating edge? | It is 0, 2 or 4. For a non-self-centered graph, two additions suffice exactly when there is a partition into two ordinary dominating sets separating the marked endpoints and keeping all distance-three pairs together. The new result has a paper proof and independent small-graph checks, not yet a Lean proof. |
| Which means occur for exactly *m* central vertices and total domination number two? | For *m* ≥ 2, set *M* = binom(*m*, 2). The attainable values are 2 − *j*/*M* for every integer *j* from *m* − 1 through *M*. The sharp maximum is 2 − 2/*m*. Every value has a realization with only two noncentral vertices. |
| Written on the Wall II, no. 269 | The ceiling inequality holds for odd total domination number and in the four-cycle-free case of total domination number two. Even values of at least four remain open here. |

The catalogue search and follow-up priority audit cover eight sources. The 2007 radius bound and the classical unconstrained center extension are prior work. The exact spectrum, specified-edge realization and sharp four-vertex lower bound are candidates for originality. The manuscript is an AI-generated research preprint.

## Formal coverage

`CenterRealization.lean` states and proves both directions of the induced-center characterization. The file also proves the advertised radius and diameter of the construction. `CenterObstruction.lean` proves the four-vertex lower bound and counts exactly four noncentral vertices in the matching construction. `CenterDomination.lean` gives the bridge to Mathlib shortest-path distances. `CenterCounts.lean` proves the pair-sum identity and a strict-average lemma. `CenterFan.lean` verifies the centers, domination and distances in the spectrum construction. The standalone finite counting and order-optimality steps of the spectrum, the general spanning-tree argument for no. 268 and the ceiling corollary remain paper proofs. The new marked two-vertex equivalence and three-to-two reduction have Lean source declarations submitted for CI verification; they are not yet certified as compiled. The integrated minimum classification remains a paper theorem.

A Lean 4.28.1 web session accepted the five source files assembled into one input and reported the dependencies of 18 declarations. [Session record](verification/lean-web.txt). The separate CI workflow builds the original module boundaries, checks each dependency list and runs Lean's independent kernel replay from an empty environment. Its job log gives the status for each commit. The baseline [CI run](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45851727702) completed with 18 checked declaration dependencies and a fresh kernel replay. The follow-up [formal coverage report](verification/formal-coverage-round2.md) records 35 intended checks (including 17 new, not yet certified) and maps the remaining semantic gaps.

## Reproduce

With Elan, Python 3.10 or newer, and an internet connection for the pinned Mathlib cache, run these commands from the repository root.

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Metric Mathlib.Tactic.DeriveFintype Mathlib.Algebra.Order.Field.Rat Mathlib.Algebra.Order.BigOperators.Group.Finset
python3 scripts/verify_lean.py
python3 experiments/enumerate_graphs.py --out reproduced.json
python3 -c "import json; assert json.load(open('reproduced.json')) == json.load(open('experiments/results.json'))"
python3 experiments/independent_check.py
python3 experiments/check_appendages.py
node experiments/check_marked_classification.js
```

The first enumerator uses integers and rational numbers. It checks 27,475 connected labelled graphs on two through six vertices, plus 240 seeded larger graphs, 833 instances of the spectrum construction and 238 specified-edge extensions. The independent checker computes distances with Floyd–Warshall and enumerates spanning trees using Prüfer words on up to five vertices. A third script examines all 32,768 labelled extensions of the four-vertex path by three vertices. Twelve have the required center and none preserves its dominating edge. With two new vertices, exactly two of the 512 labelled extensions have the required center and neither preserves the edge.

The new dependency-free Node.js check independently enumerates all 238 labelled graphs of orders 2–5 with fixed dominating edge 0–1. Counts for minima 0/2/4 are 48/170/20. For all 190 non-self-centered cases it compares the partition criterion with exhaustive two-vertex realizability; all 17 non-self-centered cases of orders 2–4 also have exhaustive three-vertex searches, with no three-only example. Four follows from the construction and classification proof, not a four-vertex exhaustive search. See [the follow-up audit](verification/marked-classification-audit.md).

Compile the manuscript with TeX Live's `pdflatex`, the Latin Modern fonts and the packages declared in its preamble.

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

For the candidate-by-candidate record, the seven score columns and the five preliminary explorations, see [the 41-row table](research/candidates.csv) and [research notes](research/selection-and-priority.md). See [LICENSE](LICENSE) for the terms of reuse.

