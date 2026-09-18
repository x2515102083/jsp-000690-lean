# Verification record and trust boundary

## Local verification observed on September 18, 2026

All three local modules (`JSP690`, `Transversal`, `Complete`) were elaborated from source with pinned stable Lean 4.32.1 and `-DwarningAsError=true`, with exit code zero. `Audit.lean` was also elaborated successfully. Its twelve named roots report only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` (or subsets). The original chromatic source is unchanged and now compiles on this stable toolchain.

`leanchecker --verbose JSP690 Transversal Complete` completed successfully, replaying all three local modules. This is normal per-module replay with imported dependencies, **not** `--fresh` replay of the full import closure. Local attempts at the latter reached their time limits and are not claimed as successful checks.

Ten fail-closed axiom-parser regression tests pass, including rejection of missing and repeated targets, malformed/truncated reports, unknown roots, `sorryAx`, native-reduction axioms and a custom axiom. The auxiliary transversal enumeration checks all 1,049,618 labelled simple three-uniform hypergraphs on 3, 4, 5 and 6 vertices; all 1,897 transversal-three-critical cases it identifies have maximum degree at most six. The original chromatic cross-check is retained as a separate auxiliary computation. These computations are not premises of the Lean proof.

The local environment used compiled imports retrieved from the exact Mathlib cache, with source snapshots rather than ordinary Git dependency checkouts. Therefore the local result is reported as direct source elaboration and replay, **not** a locally observed fresh `lake build` or successful local bootstrap.

## Reproducible CI

The workflow `.github/workflows/verify.yml` installs the official pinned Lean release archive and checks SHA-256 `57d5c062a6b4bae6fba511a1704aa124dff461c37d0fc94585637fbb7d951b50`. Its release commit is `f054605aea4b840552cca2e725580bffd1e1b704`.

A clean checkout runs `bootstrap.py` to retrieve and check all nine exact dependency revisions, then fetches compiled Mathlib imports. `scripts/verify.py` runs `lake build`, fresh warning-as-error elaboration, the twelve-root axiom audit, normal per-module kernel replay, regression tests and auxiliary computations. Dependency revisions, audited source hashes and lockfiles are checked before and after.

A run is successful only if its `verification-output/summary.json` reports `success: true` and all required workflow steps pass for the selected commit. The workflow records `GITHUB_SHA` and archives that exact source tree. Its URL and completed outcome must be read before they are used as evidence in PR #842; this source document does not predict a run's result.

## Limits

All checks are contributor-run. Leanchecker uses Lean's own kernel, not an independent kernel implementation or human mathematical referee. Imported compiled Lean/Mathlib files are trusted; this is not a source rebuild or fresh replay of every imported declaration. The separately coded Python checkers were developed in the same AI-assisted effort, not by independent reviewers. The workflow has read-only repository permissions, but no formal network-isolation attestation is made.

A source hash proves identity of bytes, not theorem correspondence or prize eligibility. Read PROOF.md, the actual definitions printed by Audit.lean, the pinned source and ATTRIBUTION.md. Organizer-designated verification, chronological priority, contribution assessment, recipient checks and any award decision remain separate and unconfirmed.
