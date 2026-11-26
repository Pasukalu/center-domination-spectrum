# Formal coverage audit — 2026-11-26, round 2

This report distinguishes committed Lean statements from successful kernel checks. It is not a release certification.

## Confirmed baseline

GitHub Actions run [45851727702](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45851727702), for commit 6e4b90886807789aad860511071006835e2e6aa7, completed successfully. The actual formalization job log was retrieved: Lean 4.28.1, Lake 5.0.0, build completed successfully (944 jobs), 18 declaration dependency closures checked, then `leanchecker --fresh CenterObstruction` completed. Only propext, Classical.choice and Quot.sound were listed. The manuscript and experiment jobs also passed.

Run [45852592895](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45852592895) includes the new marked classification paper and JavaScript experiment. At the last observation, both manuscript and experiments were successful; formalization was still running.

## New source declarations (CI pending)

Commit 926296b1831065bd2fad62c4f057b93bb80e153a: explicit two-vertex construction, exact center, preserved dominating edge, outside cardinality, and absence of a triple of pairwise far vertices.
Commit 9994e216170d9ca47e61f4a2ca2bba265532c378: necessity of the partition from two extra labels and orientation of the marked endpoints.
Commit 133a99266556b3787223483c32604dace5614fe3: marked_two_realizable_iff, using finite ambient types and exactly two distinct extra labels, for noncomplete H.
Commit 7392c03b4757493928a1da47a0db7f2e11c24500: strict_mean_of_all_dist_lt, strict_mean_of_geometric_alternatives, claim268_of_geometric_input.
Commit 68fc08009119b660d4848f7ca462b44226b45c11: marked_three_implies_two via the auxiliary distance-three path and complement of a partition; explicit disjoint exhaustive three-label definition.

The five source modules now contain 35 distinct intended dependency checks (18 baseline + 17 new). The existing forbidden-token scan found no matches. This is only a source inspection, not a replacement for compilation and axiom closure checking. Run [45853236447](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45853236447) was queued at the last observation.

## Semantic mapping and remaining gaps

| Paper result | Lean correspondence | Status |
|---|---|---|
| Metric definitions | within_iff_walk, within_iff_dist, central_iff_metric | baseline verified |
| No. 268 | Claim268; strict_mean_of_geometric_alternatives; claim268_of_geometric_input | new reduction pending CI; geometric alternatives still need proof from a total dominating set |
| Full distance spectrum | center_distance_sum; Fan.centers; Fan.spoke_distance | baseline checked sublemmas; full finite counts and sharpness theorem outstanding |
| Induced-center realization with a dominating edge | realization_iff; extension_radius_and_diameter | baseline verified |
| Four-vertex obstruction for opposite leaves | opposite_leaves_force_four; Ext.four_outside | baseline verified |
| Marked two-vertex characterization | MarkedTwoRealizable; marked_two_realizable_iff | submitted, CI pending |
| Three-to-two reduction | MarkedThreeRealizable; marked_three_implies_two | submitted, CI pending |
| Full minimum 0/2/4 theorem | above and existing four-extension proof | still requires integrated minimum/cardinality theorem, zero/one cases |
| No. 269 partial results | paper arguments | outstanding |

The new geometric reduction deliberately assumes the missing geometric statement. It must not be represented as an unconditional machine proof of No. 268. The new marked statements use exact-label witnesses; a general cardinality-to-label bridge and the integrated minimum theorem are not yet included.

No full-paper verification, original priority certification, release tag or DOI is asserted. The local Lean toolchain remains unavailable; compilation evidence comes from the specific CI commits linked above.
