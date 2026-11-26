# Marked appendage classification: follow-up audit

Date: 2026-11-26. Status: candidate paper theorem; independent mathematical proof and small finite enumeration, not fully machine-checked or priority-certified.

## Mathematical checks
The new manuscript theorem concerns the minimum number of vertices added to an induced center H while preserving a specified dominating edge uv. Self-centered H has minimum 0. Otherwise every realization has radius 2 and diameter 3, and every added vertex has an added distance-3 partner. For two new vertices the disjoint old neighborhoods are ordinary dominating sets, separate u and v, and keep all original distance-3 pairs together. Enlarging them to a partition preserves these properties. Conversely the partition gives a realization directly. For three additions the distance-3 graph on them has no isolated vertex, no triangle (each new vertex sees u or v), hence is a path. Merge its endpoints by union of their old neighborhoods; all old distances <=2 survive and the two remaining additions are still distance 3. Thus 3 cannot be the minimum. The prior four-addition construction completes the classification. This proof is graph-theoretic, not based on experimental extrapolation.

## Executed check
The same JavaScript audit function committed at experiments/check_marked_classification.js was executed in the available JS runtime before the commit. It uses bitset adjacency and exact integer distance checks (dominating edge guarantees diameter <=3). Enumerates all graphs with marked edge 0--1, requiring every other vertex adjacent to at least one endpoint. No dependence on graph atlas or original enumeration.
```
n  markedGraphs selfCentered two four threeChecked threeRealizable
2  1            1            0   0    0            0
3  3            1            2   0    2            2
4  18           3            13  2    15           13
5  216          43           155 18   0            0
```
Total 238 labelled marked graphs (not isomorphism classes); 190 non-self-centered instances checked against all possible two-addition extensions until a witness or exhaustion, 17 of order <=4 additionally checked for three additions. No discrepancy; 20 classified as four by the proof, not by enumerating every four-addition extension. The script throws on disagreement. Command: node experiments/check_marked_classification.js.

## Priority and limits
Targeted indexed search: graph centralizing number prescribed dominating edge center appendage three vertices two vertices; graph center realization two appendages partition dominating sets distance three. Buckley, Miller and Slater (1981), DOI 10.1002/jgt.3190050413, give the unrestricted appendage bound. Behrens (2015), https://digitalcommons.unl.edu/mathstudent/63/, studies classical centralizing numbers; the unrestricted parameter can take 3. Choi and Needleman (2020), https://ejgta.org/index.php/ejgta/article/view/776, study a different central-peripheral appendage parameter. These are adjacent results, not certification of priority for the marked theorem. Direct database searches and full-text comparison remain necessary.

The present environment has no lean, lake or elan; git access from the local container failed with DNS resolution of github.com. No new Lean compilation or full manuscript build is claimed. A previous commit's GitHub workflow was observed in progress; that is not evidence of successful checks on this revision. New theorem not yet Lean formalized. No license, author statement, release or submission change.
