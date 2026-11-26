# Phase III research preview

Baseline: merged PR #2, commit 9160540f83049d030e60d00add7b08d542a0e4ac. Its tested head 11e0fc43a641743fb39aacb9c1952047e1fe9433 passed [CI #39](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45853532994); actual logs showed 944 successful build jobs, 35 checked dependency closures and fresh-environment kernel replay. No disallowed dependencies in the audited closures.

## New mathematical coverage (source submitted, CI pending)

Commit 47d8af7c0601aca714f8b5ef3fee86c5f9d69bac introduces a finite ambient graph with exactly n outside vertices, measured by the actual cardinality of the noncentral-vertex finset. The minimality predicate requires existence at n and a universal lower bound for every admissible witness, not just selected constructions.

- marked_zero_iff: zero additions exactly when every old vertex is central.
- marked_one_impossible: excludes a one-vertex extension for noncomplete H.
- marked_two_of_card and marked_three_of_card: derive the exhaustive label witnesses from actual finite cardinality.
- marked_appendage_two_of_partition and marked_appendage_four: establish actual cardinality witnesses.
- marked_minimum_classification: combines these with the previously verified two-label characterization and three-to-two reduction, yielding the full 0/2/4 classification with the original paper's conditions.

There are 42 intended dependency checks (35 baseline, 7 additional). The new sources are not yet certified compiled; the mathematical target is unchanged. This document is a progress record rather than a release certificate.

## Preview acceptance gates

- [ ] All current Lean declarations compile and pass dependency audit and fresh kernel replay.
- [ ] General geometric argument for No. 268 formalized, including total dominating set and spanning-tree construction.
- [ ] Full finite counting, attainability and sharpness of the center distance spectrum formalized.
- [ ] Existing No. 269 partial result formalized.
- [ ] Regenerate committed manuscript PDF from the matching LaTeX source.
- [ ] All research experiments and manuscript builds succeed; README describes actual coverage.

Priority review and human scholarly review remain publication gates. No release, DOI, authorship or license changes are authorized by this branch.
