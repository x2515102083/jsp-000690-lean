# Verification record

## Scope and trust boundary

This is a submitter-run verification record for `JSP690.jsp000690`, not an
official prize verification decision and not independent human peer review.
The exact statement and its interpretation are described in [README.md](README.md).
Mathematical and prior-formalization credits are in [ATTRIBUTION.md](ATTRIBUTION.md).

## Pinned environment

- Lean: `leanprover/lean4:v4.35.0-rc2`.
- Lean release commit: `11acb17ec6b07a8f9e9173e6845197929540936b`.
- Lake: bundled Lake 5.0.0.
- Local test platform: Windows x86-64.
- Dependencies: bundled Lean/Std only; `lake-manifest.json` has no packages.
- `decide` uses kernel reduction. No native-code decision axiom is used.
- This is a release-candidate toolchain. Maintainer approval of its safety or
  acceptability has not been obtained; no such approval is implied.

## Observed local checks, 2026-09-18 (Asia/Shanghai)

The full `scripts/verify.py --clean` run completed with all commands successful,
including a clean build and all seven axiom-parser tests. Both
`lake env leanchecker --verbose JSP690` and
`lake env leanchecker --fresh --verbose JSP690` completed successfully.
The second command replays imported and project declarations into a fresh
environment. `leanchecker` uses Lean's own kernel; it is **not** an independently
implemented proof checker. No nanoda/lean4lean result or sandbox isolation
certification is claimed.

`lake env lean Audit.lean` printed the following dependency sets:

| Declaration | Axioms |
| --- | --- |
| `binaryColorings_complete` | `propext`, `Quot.sound` |
| `binary_obstruction` | `propext` |
| `edge_deletion_certificates` | `propext`, `Classical.choice`, `Quot.sound` |
| `vertex_deletion_certificates` | `propext`, `Classical.choice`, `Quot.sound` |
| `liGraph_chromatic_number` | `propext`, `Quot.sound` |
| `liGraph_all_proper_subgraphs` | `propext`, `Classical.choice`, `Quot.sound` |
| `liGraph_deleted_edge_chromatic_two` | `propext`, `Classical.choice`, `Quot.sound` |
| `liGraph_deleted_vertex_chromatic_two` | `propext`, `Classical.choice`, `Quot.sound` |
| `jsp000690` | `propext`, `Classical.choice`, `Quot.sound` |

The fully qualified namespace is `JSP690`. No final audited declaration depends
on `sorryAx`, `Lean.ofReduceBool`, or a project-defined mathematical axiom.

The separate Python cross-check confirmed all 512 binary colorings fail, an
explicit three-coloring succeeds, all 22 edge deletions and all 9 vertex deletions
admit binary colorings, and the vertex degrees are `(10,7,7,7,7,7,7,7,7)`.
The Python calculation is corroboration, not a premise of any Lean theorem.

## Reproducibility and limitations

Run `python3 scripts/verify.py --clean` to repeat all local checks. The script
checks subprocess exit codes; the axiom parser requires all nine reports and
rejects unexpected axioms. Parser tests also check rejection of missing reports,
duplicate reports, explicit Lean errors, placeholder axioms, native trust, and
custom axioms.

The public workflow rebuilds on a Linux runner using the pinned toolchain and
without project build-cache reuse. Workflow success, when present, is additional
machine evidence, not official award review. Consult the actual workflow run
rather than interpreting the existence of the workflow as proof it ran.

This project does not certify Lean/Std's implementation, settle prize priority,
verify recipient identity, or authorize a payment. Earlier formalizations exist.
