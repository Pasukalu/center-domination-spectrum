# Independent mathematical review packet

**Review requested, not completed.** This packet is for a qualified independent graph theorist. No reviewer has been contacted or credited. The project is an extensively AI-generated research preprint; the purpose of the review is to identify errors, prior work, missing hypotheses and actual mathematical contributions, rather than endorse a predetermined conclusion.

## Immutable material and scope

- Frozen [v0.9.0](https://github.com/Pasukalu/center-domination-spectrum/releases/tag/v0.9.0), commit `4f0709f68fa4a9a1e9e012a1135b29f438d12d1c`.
- [Final packaging CI #133](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45873013098): 1,187 build jobs, 84 audited declaration dependencies, independent fresh kernel replay; all experiment and manuscript jobs succeeded.
- Current Phase IV branch changes attribution and review documents; the revised PDF was archived in `9c2c6c6bc37de2bf70017c5ccfffa362f9f3f292` after successful [archive run](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45878046555). Independent binary retrieval verified the 290,181-byte PDF SHA-256 `fcc2c0ca23ae49470013dfc8cc44aaa489970f7f11f6c9a1df3f534d01837ea2`. The frozen v0.9.0 release remains unchanged.
- The five Lean files, toolchain, Mathlib manifest, verification script and regular CI workflow were compared with the frozen revision using their Git blob IDs; all nine match. No proofs were modified in this comparison.
- Reproduce using README. The verified public declarations in the five modules number 6, 40, 11, 2 and 25 respectively (84 total). Axiom closure allowlist: propext, Classical.choice, Quot.sound.

## Statement-to-proof map

All Lean names below are in namespace CenterDomination. The exact definitions, not English names alone, determine the certified claim.

| Manuscript | Lean source and declarations | Coverage / issue to check |
|---|---|---|
| Definitions, §1 | CenterDomination: within_iff_dist, central_iff_metric; CenterCounts: meanCenter, centerPairs | Ambient shortest-path distance; connectedness; ordered distinct pairs versus unordered mean; rational zero for an empty sum/denominator (singleton). |
| Lemma 2.1 (component-sensitive spanning tree) | CenterCounts: exists_bounded_spine, exists_bounded_spine_tree, tree_midpoint_covers, spine_cover_lift | Alternative parity-sensitive spine proof; the sharper k+2c−1 lemma as printed is not independently formalized. The 2007 article proves the minimum-set bound. |
| Theorem 2.2 (no. 268) | CenterCounts: claim268, strict_mean_of_spanning_midpoints, mean_center_le_pred_of_odd_total_dom | Claim268 quantifies over every total dominating set of a finite connected graph, not an assumed optimal set. Floor reformulation is elementary, not a separate formal declaration. |
| Theorem 3.1 (spectrum) | CenterCounts: center_pairs_card_choose, center_adj_pairs_card, center_graph_connected, center_edge_count_bounds, center_mean_edge_formula, spectrum_necessity, spectrum_upper_bound, spectrum_max_iff_tree; CenterFan: spectrum_attainment, spectrum_exact, spectrum_max_attained; CenterObstruction: proper_center_order_bound | Actual induced graph edge count and ambient rational distance. Exact spectrum existence quantifies over Type (universe zero); necessity and pointwise bounds are universe-polymorphic. The ambient order bound assumes a noncentral vertex. |
| Theorem 3.2 (realization) | CenterRealization: realization_iff, extension_radius_and_diameter; CenterDomination: Ext.exact_centers, Ext.realizes_center; CenterObstruction: Ext.four_outside | Realizable means an induced embedding into a finite connected graph with a dominating edge and exactly the embedded center. Radius and diameter are stated via walk-length coverage. |
| Theorem 3.3 (four necessary) | CenterObstruction: opposite_leaves_force_four, Ext.four_outside | Lower bound for opposite center leaves; verify the distinctness and leaf hypotheses. The ordinary centralizing-number-two double-star comparison is a paper argument, not separately claimed as an audited integrated theorem. |
| Theorem 3.4 (marked minimum) | CenterObstruction: marked_zero_iff, marked_one_impossible, marked_two_realizable_iff, marked_three_implies_two, marked_appendage_two_of_partition, marked_appendage_four, marked_minimum_classification | MarkedAppendage quantifies over finite ambient graphs, injective induced embeddings, exact center, the retained dominating edge and actual outside cardinality. MarkedMinimum includes attainment and lower bound over all feasible cardinalities. |
| Corollary 4.1 (partial no. 269) | CenterCounts: center_clique_of_noFourCycle, mean_center_le_one_of_noFourCycle, claim269_partial | Odd total domination cardinality or cardinality two plus NoFourCycle. NoFourCycle excludes ordinary cycles, including cycles with chords. The general even case ≥4 is not solved. Ceiling translation not separately formalized. |

## Specific mathematical questions for the reviewer

1. **Definition alignment.** Does the original Graffiti.pc catalogue use the same mean over distinct central pairs and singleton convention? Check the original catalogue, not merely a secondary citation. Does the finite simple graph convention exclude any intended cases?
2. **No. 268.** Reconstruct the proof independently using the prior 2007 spanning tree bound. If ambient radius equals k, both adjacent tree midpoints must remain central in G; every central pair has distance ≤k and one pair has distance 1<k. Check k≥2 and the r<k/singleton cases. Is this conclusion already explicitly stated in earlier literature?
3. **Component bound.** The quotient-tree proof selects crossing edges between connected parts assigned to components of a total dominating set, adds at most 2(c−1) endpoints, and attaches outside vertices as leaves. Verify connectedness, no repeated vertices on tree paths, and the arbitrary-set extension; distinguish this from the known minimum-set bound.
4. **Exact spectrum.** Verify both radius cases, the connected induced center, and e=m−1 iff a tree. Check the K_{2,m−1} plus pendant construction for m=2, t=0 and t=binom(m−1,2); ensure no added vertex becomes central. Confirm that minimal order refers to proper centers only. A self-centered complete graph may realize mean 1 on m vertices.
5. **Four-vertex realization.** Audit every adjacency of P,Q,A,B. Ensure all old vertices have eccentricity exactly two, P/A and Q/B are distance three, and the original marked edge totally dominates every vertex.
6. **Marked 0/2/4.** Verify the necessity of disjoint old neighborhoods for two new vertices, domination of closed neighborhoods, and the distance-three pair criterion. For three new vertices check the auxiliary distance-three graph has no isolated vertices and no triangle. Verify merging its two endpoints preserves all old-old and old-new paths of length at most two; no old vertex becomes universal. Check zero versus self-centered and the noncomplete assumption.
7. **Ceiling result.** Check both odd and C4-free cardinality-two arguments, in particular whether two exclusive sides can have a common neighbor. Do not assume an induced C4 prohibition suffices. Identify any overlooked even case without claiming the entire conjecture.
8. **Priority.** Compare the marked constraint with classical center realization/centralizing-number and related peripheral or edge-deleted appendage parameters. Identify exact earlier statements, not merely similar terminology. Assess whether the spectrum result is separately known or an immediate standard corollary.

## Reviewer response form (to be completed by the reviewer)

For each of questions 1–8: verdict (correct / minor repair / major repair / counterexample / not assessed), exact statement or line, independent argument or counterexample, cited source if relevant, suggested revision. Provide separate novelty verdict (known / straightforward consequence / potentially distinct / unresolved), and record review date and scope. A review report is not consent to be a coauthor or to be publicly named.

## Limitations and next steps

This packet does not certify novelty, peer review, or authorship. No reviewer identity is asserted. The Phase IV priority report and journal-policy review document the remaining literature-access and policy limitations. Human contribution records, expert review, final attribution, final-head CI are required before a publication-ready version. Do not register a DOI or submit to a journal without authorization.
