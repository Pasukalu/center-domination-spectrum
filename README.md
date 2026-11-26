# Distances between central vertices in graphs with small total domination number

[Read the four-page manuscript](paper/main.pdf) · [LaTeX source](paper/main.tex) · [Selection and priority audit](research/selection-and-priority.md) · [Proof review](verification/proof-review.md) · [Research checks](../../actions/workflows/research.yml)

Let *C* be the vertices of minimum eccentricity in a finite connected simple graph, and let `mean(C)` average their ambient distances over distinct unordered pairs. The manuscript uses zero for a singleton center. A dominating edge is an edge whose endpoints together supply a neighbor to every vertex.

| Question | Result |
| --- | --- |
| Written on the Wall II, no. 268 | The mean is strictly smaller than the minimum size of a total dominating set. This gives the proposed floor inequality. The paper gives a spanning-tree proof. |
| Which graphs occur as an induced center when the total domination number is two? | A finite graph with at least two vertices occurs exactly when it contains a dominating edge. Every specified dominating edge is preserved in an explicit realization with four additional vertices, radius two and diameter three. |
| Which means occur for exactly *m* central vertices and total domination number two? | For *m* ≥ 2, set *M* = binom(*m*, 2). The attainable values are 2 − *j*/*M* for every integer *j* from *m* − 1 through *M*. The sharp maximum is 2 − 2/*m*. Every value has a realization with only two noncentral vertices. |
| Written on the Wall II, no. 269 | The ceiling inequality holds for odd total domination number and in the four-cycle-free case of total domination number two. Even values of at least four remain open here. |

The catalogue search and follow-up priority audit cover eight sources. The 2007 radius bound and the classical unconstrained center extension are prior work. The exact spectrum and specified-edge result are candidates for originality. The manuscript is an AI-generated research preprint.

## Formal coverage

`CenterRealization.lean` states and proves both directions of the induced-center characterization. The file also proves the advertised radius and diameter of the construction. `CenterDomination.lean` gives the bridge to Mathlib shortest-path distances. `CenterCounts.lean` proves the pair-sum identity and a strict-average lemma. `CenterFan.lean` verifies the centers, domination and distances in the spectrum construction. The standalone finite counting and order-optimality steps of the spectrum, the general spanning-tree argument for no. 268 and the ceiling corollary are currently paper proofs.

A Lean 4.28.1 web session accepted the four source files assembled into one input and reported the dependencies of 16 declarations. [Session record](verification/lean-web.txt). The separate CI workflow builds the original module boundaries, checks each dependency list and runs Lean's independent kernel replay from an empty environment. Its job log gives the status for each commit.

## Reproduce

With Elan, Python 3.10 or newer, and an internet connection for the pinned Mathlib cache, run these commands from the repository root.

```sh
lake exe cache get
python3 scripts/verify_lean.py
python3 experiments/enumerate_graphs.py --out reproduced.json
python3 -c "import json; assert json.load(open('reproduced.json')) == json.load(open('experiments/results.json'))"
python3 experiments/independent_check.py
```

The first enumerator uses integers and rational numbers. It checks 27,475 connected labelled graphs on two through six vertices, plus 240 seeded larger graphs, 833 instances of the spectrum construction and 238 specified-edge extensions. The independent checker computes distances with Floyd–Warshall and enumerates spanning trees using Prüfer words on up to five vertices.

Compile the manuscript with TeX Live's `pdflatex`, the Latin Modern fonts and the packages declared in its preamble.

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

For the candidate-by-candidate record, the seven score columns and the five preliminary explorations, see [the 41-row table](research/candidates.csv) and [research notes](research/selection-and-priority.md). See [LICENSE](LICENSE) for the terms of reuse.

