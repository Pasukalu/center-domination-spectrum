# Phase III research preview

Baseline: merged PR #2, commit 9160540f83049d030e60d00add7b08d542a0e4ac. Its tested head 11e0fc43a641743fb39aacb9c1952047e1fe9433 passed [CI #39](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45853532994); actual logs showed 944 successful build jobs, 35 checked dependency closures and fresh-environment kernel replay. No disallowed dependencies in the audited closures.

## New mathematical coverage (source submitted, CI pending)

Commit 47d8af7c0601aca714f8b5ef3fee86c5f9d69bac introduces a finite ambient graph with exactly n outside vertices, measured by the actual cardinality of the noncentral-vertex finset. The minimality predicate requires existence at n and a universal lower bound for every admissible witness, not just selected constructions.

- marked_zero_iff: zero additions exactly when every old vertex is central.
- marked_one_impossible: excludes a one-vertex extension for noncomplete H.
- marked_two_of_card and marked_three_of_card: derive the exhaustive label witnesses from actual finite cardinality.
- marked_appendage_two_of_partition and marked_appendage_four: establish actual cardinality witnesses.
- marked_minimum_classification: combines these with the previously verified two-label characterization and three-to-two reduction, yielding the full 0/2/4 classification with the original paper's conditions.

There are now 50 intended dependency checks (42 verified in CI #48, 8 additional pending). The new sources are not yet certified compiled; the mathematical target is unchanged. This document is a progress record rather than a release certificate.

## Preview acceptance gates

- [ ] All current Lean declarations compile and pass dependency audit and fresh kernel replay.
- [ ] General geometric argument for No. 268 formalized, including total dominating set and spanning-tree construction.
- [ ] Full finite counting, attainability and sharpness of the center distance spectrum formalized.
- [ ] Existing No. 269 partial result formalized.
- [ ] Regenerate committed manuscript PDF from the matching LaTeX source.
- [ ] All research experiments and manuscript builds succeed; README describes actual coverage.

Priority review and human scholarly review remain publication gates. No release, DOI, authorship or license changes are authorized by this branch.

## Follow-up CI and ceiling case

[Run #46](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45856383079) passed experiments and manuscript but failed Lean at `marked_zero_iff`: the implicit injectivity arguments needed explicit application. The log also reported three simplification warnings. Commit `a037552878ca808f698689e360c31c1bbe60f1b4` addresses those diagnostics; the full rerun remains to be confirmed.

Commit `9b94c84970207039359d0bed55e699db3aa10455` adds `NoFourCycle`, `center_clique_of_noFourCycle`, and `mean_center_le_one_of_noFourCycle`. The latter proves the actual rational center mean is at most one when a dominating edge exists and no simple four-cycle exists. This covers the graph-theoretic k=2 part of No. 269, pending CI. The odd-k case still depends on the general geometric argument. The general No. 268 construction remains outstanding.

## Confirmed minimum theorem and geometric transfer

[CI #48](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45856994349) succeeded on commit `a037552878ca808f698689e360c31c1bbe60f1b4`. Actual logs confirm 944 successful Lake build jobs, 42 audited dependency closures, and fresh kernel replay; `marked_minimum_classification` depends only on propext, Classical.choice and Quot.sound. The complete marked minimum classification is machine checked at this commit.

[CI #52](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45857104592) failed in the subsequently added ceiling proof: symmetry of a negated equality and unavailable norm_num. Commit `2534007a16a3bd7bacaa6bec2ddac2fadf76aa90` corrects these. Verification of the fix remains pending.

Commit `c2118d5ae73daa26b8babc1cf78689c8ae8e731f` adds six audited statements: mean bound from a covering ball, centrality from a minimal cover, strict mean from two adjacent covering vertices, transfer of bounded walks along edge inclusion, strict mean from a spanning midpoint certificate, and the unconditional dominating-edge case. The general total-domination-to-bounded-spanning-tree construction and the midpoint certificate existence remain unproved in Lean. This transfer is not a full proof of No. 268. The 50-declaration revision is pending CI.

## Constructive spanning-spine certificate experiment

Commit `02a2296f80eb4613ede3ffc595c6e035ffb2a7c8` implements the manuscript's Lemma 2.1 directly: compute components of G[D], assign each external vertex to an adjacent component, construct a quotient spanning tree, add crossing endpoints to K, construct a tree on K and attach the remaining leaves. Independent BFS on the resulting tree verifies edge inclusion, connectivity, edge count, component and diameter bounds, midpoint radius, odd-k radius improvement and the adjacent-center equality case.

The implementation was executed in the JavaScript runtime before commit, with no failures: orders 2–5 exhaust every total dominating set; order 6 exhausts every minimum total dominating set. Counts by order are 1, 13, 258, 9793, 90300 certificates (100365 total) over 27475 connected labelled graphs. The constructed tree attained diameter 2k−1 in 62928 cases. This is finite testing, not the universal Lean proof. The saved Node script contains expected per-order counts; CI execution of the saved file is pending.

## Verified 50-declaration baseline

[CI #59](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45858117974) passed all three jobs on `d6254203ec6779646743c261898cc11faa74c38a`. The retrieved formalization job log confirms 944 Lake build jobs, 50 checked dependency closures, and fresh kernel replay. In particular `mean_center_le_one_of_noFourCycle`, `strict_mean_of_spanning_midpoints`, and `mean_center_lt_two_of_domEdge` have only standard permitted dependencies. The subsequent experiment and documentation commits await their own CI result. The universal spanning-tree existence and tree midpoint argument, spectrum counting, and updated PDF remain preview gates.

## Finite-induction spine construction (pending CI)

[CI #67](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45858795122) passed on `dfddcf864774c01b42d8d02f0716400e89a1a74d`, including the saved constructive Node regression and all 50 audited closures plus fresh kernel replay.

Commit `18654262c9ebd94bb6465543945c2a9b9c28a54c` adds `SpineBuilt`, an explicit finite vertex insertion certificate, and `exists_bounded_spine`. This uses a different but equivalent-for-the-radius-bound construction from the component quotient in the manuscript. Starting from two adjacent D vertices, keep S ⊆ D and S ⊆ K with K.card + 2 + S.card % 2 ≤ 2 * S.card. A single unprocessed D vertex already in or adjacent to K costs at most one insertion. Otherwise a walk crosses from the closed neighborhood of S to its complement; the next vertex has a D neighbor x outside S and x has a D neighbor t outside S. Insert the crossing endpoints and x,t, costing at most four insertions for two new D vertices. Strictly decreasing D.card - S.card terminates the construction. The target is a connected insertion certificate containing D with K.card ≤ 2k−2, or ≤ 2k−3 for odd k. This does not yet formalize the sharper component-sensitive bound k+2c−2, the attachment-tree construction, or the tree midpoint theorem. The new source is pending CI (51 intended audited declarations, 50 verified at the prior commit).

## Verified spine tree and unconditional Claim268 candidate

[CI #76](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45861050185) succeeded on `5c461fd7312d8ded4f5a80010a3765b9f7e3465f`. The actual Lean job log reports 1187 successful Lake build jobs, 55 checked dependency closures, and fresh kernel replay. In particular `exists_bounded_spine`, `SpineBuilt.induced_connected`, `exists_bounded_spine_tree`, and `total_dom_card_ge_two` have only the allowed standard dependencies.

Commit `c29e2b0df12c6607b794d0c280efbdee2c8f6493` adds seven audited declarations. `tree_unique_closer` derives uniqueness of a closer neighbor from tree path uniqueness; `no_peak_sequence_bound` proves an arithmetic unit-step bound; `tree_longest_path_bound`, `tree_has_longest_path`, and `tree_midpoint_covers` connect that to actual Mathlib tree distances; `spine_cover_lift` uses total domination to extend any covering ball by one step into the whole ambient graph. Finally `claim268` has exactly the existing unconditional `Claim268 G` conclusion, requiring no geometric hypothesis beyond the original connected finite graph and total dominating set. These are submitted source declarations, not yet confirmed by compilation. The sharper component-sensitive lemma in the paper and odd-k strengthened bound are not yet integrated; the spectrum and refreshed PDF remain outstanding. 62 intended audited declarations, 55 confirmed in CI #76.

## Unconditional Claim268 verified

[CI #82](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45863839856) succeeded on `bbcca66c827e8cdf042653cad24e0ba789511ff5`. All three jobs succeeded. The retrieved formalization log shows 1,187 build jobs, 62 audited dependency closures and fresh kernel replay. `CenterDomination.claim268` depends only on propext, Classical.choice, Quot.sound. The final theorem is unconditional with respect to the geometry; `Claim268 G` quantifies over every total dominating set of a connected finite graph. This is not a literature-priority certificate, and the paper's stronger component-count lemma is not separately formalized.

Commit `dc78b564115a4b71fc644c1c27437fe60086d917` adds `odd_total_dom_cover`, `mean_center_le_pred_of_odd_total_dom` and `claim269_partial`. The final statement combines odd cardinality with the no-four-cycle case of cardinality two, proving the rational bound underlying the ceiling inequality. These three declarations are pending CI; the intended audit total is 65. No claim about the remaining even cardinalities at least four is made. Spectrum counting and regenerated manuscript remain preview gates.

## Verified partial Claim269 and spectrum development

[CI #87](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45864787755) passed on `fa932764b60e2ba33cea0244511bca4726bc11d2`. Actual logs confirm 1,187 build jobs, 65 audited dependency closures, and fresh kernel replay, including `claim269_partial` with only the allowed dependencies. [CI #89](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45865028840) failed on the spectrum revision: `centerPairs` and `centerRelPairs` were not definitionally equal. Commit `744fcecc8424f1a3aeda48a6589c5ea34eb54e7b` replaces the conversion with an explicit finite-set equality. The other new counting declarations had no independent compilation error, but the failed build does not certify them.

Commit `08130e1695f523f8b2ed35b37cb0f688a83211bb` adds five audited statements: actual fan center cardinality, induced edge cardinality, ambient cardinality, existence of a graph with any prescribed admissible number of edges, and `spectrum_attainment` for every admissible j on exactly m+2 vertices. Commit `0d32c64fdf087fc49e2482a39db7f825401cbfd2` adds `proper_center_two_outside` for the lower bound on the number of noncentral vertices (both radius-one and radius-two cases). These sources have not yet passed CI. The intended total is 77 audited statements, with 65 certified at the prior commit. The equality-at-maximum tree characterization, integration of the exact spectrum theorem, current PDF and final review remain outstanding.

## Spectrum integration, pending successful build

[CI #98](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45866459105) passed the experiment and manuscript jobs but failed at the simplifier in `center_pairs_card_choose` (maximum recursion depth). Commit `584fe7ebf44e3bda60c5654e0fca2f2a62815c06` replaces broad simplification with explicit subtype equality and restricted rewrite rules. CI #100 for that fix is still in progress at the time of this update.

Commit `bda0c28ab601224367bf400b5eb1bce8e4728b41` adds four statements: minimum edge density simplification, spectrum necessity, the sharp upper bound and equality iff the induced center is a tree. Commit `210134c71317ba10a76f52096fec4ffb1c162890` integrates both directions into `spectrum_exact` and constructs the sharp maximum on m+2 vertices. Commit `668e7297ddd8b16ab6cf77979544957d797aa3cf` connects the outside-cardinality lower bound to the actual ambient graph order. These are submitted Lean sources, not certified results. There are 84 intended audited declarations; the last confirmed complete run remains #87 with 65. The full spectrum, equality characterization and order optimality are pending successful CI; PDF refresh, priority review and release preparation remain outstanding.

## Phase III complete mathematical verification baseline

[CI #114](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45869576150) succeeded on `2964edf0e1fc30dd77104ca050694ddac6d2c79d`. Retrieved the actual formalization job log (job 140081184156): `Build completed successfully (1187 jobs).` and `Checked 84 axiom closures and replayed the module from a fresh environment.` The experiment and manuscript jobs also succeeded. The last fixes were explicit subtype equality, explicit finite image counts, direct instantiation of the handshaking identity, and preservation of the two outside-vertex witnesses during membership case analysis. No hypothesis was weakened to achieve compilation. In particular, `claim268`, `claim269_partial`, `marked_minimum_classification`, `spectrum_exact`, `spectrum_max_iff_tree`, and `proper_center_order_bound` depend only on propext, Classical.choice and Quot.sound.

The successful run produced [manuscript-pdf](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45869576150/artifacts/15142406315), artifact ZIP SHA-256 `e49ccdbbd41dbaf377e21b2a8d44a9fb7900c1c9b163fa9f476d49d9f49ab932`, and [lean-diagnostics](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45869576150/artifacts/15141857898), artifact ZIP SHA-256 `fb0f7c47c9207adeeb988a10ad174b4bdd3e5ed0777475586cb2afddba056b91`. These digests are the metadata reported by GitHub, not locally recalculated. The old checked-in PDF is not the current manuscript. The subsequently edited LaTeX research record must be recompiled. CI #114 certifies the source revision named above, not subsequent documentation changes. No new mathematical source declarations have been added. Publication priority, human expert review, final PDF replacement and publication decisions remain separate gates. No claim of solving the remaining even no. 269 cases is made.
