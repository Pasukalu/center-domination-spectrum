# Phase IV — v0.9.0 research preview packaging

## Verified baseline

- PR #3 merged into main as `9d3b9b322d44f2ee9e1c7567b5dab0bd1c6db0f9`.
- [CI #120](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45871760984) passed all three jobs on pre-merge head `349fdc8e2d06b199b7eae2bab04459bad8fc25ed`: 1,187 Lake build jobs, 84 dependency closures and independent fresh kernel replay.
- [CI #120 manuscript artifact](https://github.com/Pasukalu/center-domination-spectrum/actions/runs/45871760984/artifacts/15141784638) ZIP SHA-256 reported by GitHub: `1291bd2dfa01a5fb5987535ea18fbd7fee0782d559ef2af8ce6a0afb7a3f8b4d`.
- The connector's PR workflow query does not enumerate push-only runs on main. Do not infer post-merge CI success from an empty response.

## Release gates

- [x] Core mathematical source checks on verified PR head.
- [x] PR #3 merged.
- [x] Rebuild and commit the matching PDF and SHA-256 manifest.
- [ ] Verify the exact packaging branch through the standard research checks.
- [ ] Merge the packaging PR.
- [ ] Publish v0.9.0 as an explicitly labeled research prerelease, not a peer-reviewed article.

## Scope and publication limits

The verified results include the unconditional rational inequality corresponding to no. 268, the stated partial no. 269 cases, the marked 0/2/4 classification, the exact rational distance spectrum, its extremal tree condition and proper-center order bound. The sharper component-sensitive lemma is not separately formalized; the floor and ceiling translations are elementary consequences. Even no. 269 cases at least four remain unresolved here. These checks establish the formal statements, not literature priority. Human expert review, authorship/accountability and journal-policy review, and any Zenodo DOI or submission are separate decisions; no DOI or submission is claimed.

The release packaging branch must not modify mathematical statements or weaken CI. The one-off branch-restricted workflow committed `paper/main.pdf` and its manifest in `6b7c9ab5d2eed6db22cd1c23509457e9f560c135`. Independent retrieval of the committed binary confirmed its PDF-1.7 header, 289,774-byte size, and SHA-256 `0f932395d96ef35749eb01b372d1acc69fb50b14e7d22edfbcc98bf7ad83170f`, matching the manifest. PR CI #127 on the bot commit concluded action_required without any jobs; this is not a mathematical failure or successful validation. The temporary write-enabled archival workflow is being removed, and the regular read-only research workflow checks the archived checksum. Final-head checks are still required.
