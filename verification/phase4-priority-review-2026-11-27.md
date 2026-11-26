# Phase IV — priority review (2026-11-27)

## Frozen release

The public [v0.9.0 prerelease](https://github.com/Pasukalu/center-domination-spectrum/releases/tag/v0.9.0) was confirmed using the GitHub releases API, with prerelease=true, draft=false, target and tag both resolving to `4f0709f68fa4a9a1e9e012a1135b29f438d12d1c`. The PDF asset is 289,774 bytes and GitHub reports SHA-256 `0f932395d96ef35749eb01b372d1acc69fb50b14e7d22edfbcc98bf7ad83170f`, matching the independently checked repository binary. The publication workflow completed successfully (run 45874723143). The exact packaging PR passed [CI #133](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45873013098), including all 84 named axiom closures and fresh kernel replay. No academic DOI or submission was made.

## Targeted literature checks

1. [Written on the Wall II, catalogue PDF](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf), snapshot dated November 6, 2026, printed p. 156: nos. 268 and 269 were announced February 23, 2007, and marked open in that snapshot. No. 268 concerns the floor of one plus the ambient mean of distinct central pairs; no. 269 replaces floor with ceiling under the additional C4-free restriction. The indexed PDF text was retrieved; a page-image fetch returned 404, so no page-image inspection is claimed. This snapshot is evidence of catalogue status, not proof of priority or present-day open status.
2. DeLaViña, Liu, Pepper, Waller and West, *Some conjectures of Graffiti.pc on total domination*, Congressus Numerantium 185 (2007), 81–95 ([author-uploaded text](https://www.researchgate.net/publication/247768453_Some_conjectures_of_Graffitipc_on_total_domination)). Lemma 2 supplies a spanning tree preserving a minimum total dominating set. Lemma 3 explicitly bounds the diameter of that tree by k+2c−1≤2k−1, where k is the minimum total domination cardinality and c counts components of the chosen set. Thus the component-sensitive diameter inequality for minimum sets is already present; the manuscript's derivation for arbitrary total dominating sets must not be advertised as a new bound in the minimum case. The existing proof also uses adjacent tree centers. The strict mean conclusion follows by observing that an adjacent central pair makes the average strictly less than the radius when radius=k. The new contribution, if priority is confirmed, is the application to the exact catalogue statement, not the foundational radius/diameter bound.
3. Buckley, Miller and Slater, *On graphs containing a given graph as center*, J. Graph Theory 5 (1981), 427–434, [DOI](https://doi.org/10.1002/jgt.3190050413), [publisher issue](https://onlinelibrary.wiley.com/toc/10970118/1981/5/4): classical unrestricted appendage upper bound four and tree classification. Do not claim the unrestricted construction or general appendage number as new.
4. Sarah Lynne Behrens, *Graph Centers, Hypergraph Degree Sequences, and Induced-saturation* (2015), [institutional thesis record](https://digitalcommons.unl.edu/mathstudent/63/): related centralizing-number literature; metadata and abstract checked, complete thesis not reviewed in this pass.
5. [Classifying trees with edge-deleted central appendage number 2](https://www.dml.cz/handle/10338.dmlcz/140644), 2009: related but distinct center-embedding restriction; bibliographic trail to Bielak, *Minimal realizations of graphs as central subgraphs*. Obtain and compare full texts before claiming priority for the marked problem.

Search phrases included "average distance" + "central vertices" + "total domination"; "centralizing number" + graph center; "specified dominating edge" + center realization; arXiv-restricted variants; and the original paper's title/authors. No exact duplicate of the marked 0/2/4 partition criterion or full rational spectrum was identified in this limited search. Search results also included unrelated conjectures involving distances from minimum-degree vertices: they must not be confused with no. 269. No exhaustive MathSciNet, zbMATH, Crossref or Google Scholar coverage or independent expert review has been established.

## Contribution assessment

| Claim | Status |
|---|---|
| Radius bound and component diameter bound for minimum total dominating sets | Prior work, explicitly credited |
| No. 268 strict mean conclusion | Verified; short consequence of prior geometric bounds; priority not certified |
| No. 269 odd case and C4-free cardinality-two case | Verified partial result; remaining even cases not solved here |
| Unrestricted appendage upper bound four | Classical prior work |
| Marked-edge-preserving 0/2/4 classification and partition criterion | Strongest candidate for distinctive contribution; full related-literature review needed |
| Exact central-pair distance spectrum and extremal tree condition | Verified candidate contribution; compare existing central ratio and distance-defined subgraph literature |

## Before v1.0.0

- Obtain expert review of the precise marked-edge restriction and spectrum, with explicit counterexample/definition checks.
- Clarify the attribution of Lemma 2.1 in the next manuscript revision, including the precise 2007 minimum-set bound; do not change the frozen v0.9.0 tag.
- Check publisher AI policies and authorship eligibility, have accountable human contributors approve the manuscript, and disclose actual AI assistance accurately.
- Make no DOI registration or journal submission without user confirmation.
