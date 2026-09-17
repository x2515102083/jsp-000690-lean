# JSP-000690: complete chromatic-critical hypergraph formalization

This Lean 4 project proves the **chromatic** formulation of
[JSP-000690](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000690):
there exists a simple 3-uniform hypergraph with chromatic number exactly 3,
every proper subhypergraph 2-colorable, and minimum degree at least 7.

The mathematical construction is **Ruiliang Li's**, not a new discovery here.
It is the nine-vertex, twenty-two-edge graph in equation (5) of
[arXiv:2512.24850v1](https://arxiv.org/html/2512.24850v1#S4).
The minimum degree is exactly 7; the degrees are `(10,7,7,7,7,7,7,7,7)`.

This is a later, separately written formalization prepared with OpenAI Codex
for the GitHub account `x2515102083`. Earlier formalizations and submissions
exist. **No first-formalization priority, independent human review, new
mathematical solution, or award entitlement is claimed.** See
[ATTRIBUTION.md](ATTRIBUTION.md) for the disclosure and prior-work links.

## Reproduce

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone --branch proof-jsp-000690 https://github.com/x2515102083/jsp-000690-lean.git
cd jsp-000690-lean
lake build
lake env lean Audit.lean
lake env leanchecker --verbose JSP690
lake env leanchecker --fresh --verbose JSP690
python3 scripts/crosscheck.py
```

Alternatively, `python3 scripts/verify.py --clean` performs a clean build,
the fail-closed axiom audit, both replay modes, the finite cross-check, and
seven regression tests of the audit parser, checking every exit status.

For a fail-closed axiom allowlist check (Bash):

```sh
set -o pipefail
lake env lean Audit.lean | python3 scripts/audit_axioms.py
```

The toolchain is pinned to `leanprover/lean4:v4.35.0-rc2`, release commit
`11acb17ec6b07a8f9e9173e6845197929540936b`. This is an explicitly pinned
release candidate, not a claim that prize maintainers have approved that version.
Only bundled `Std`/Lean libraries are imported. **No Mathlib and no external
Lake packages are required.** The Python scripts require only the standard
library and are not used to construct or justify the Lean proof.

## What the theorem actually proves

The entry point is `JSP690.jsp000690` in [JSP690.lean](JSP690.lean).

| Mathematical requirement | Lean declaration / representation |
| --- | --- |
| Finite vertex set | `Fin 9`; the paper's labels `1..9` become `0..8` |
| Simple 3-uniform hypergraph | `liGraph_simple`: duplicate-free list of strictly increasing triples |
| All binary colorings fail | `binary_obstruction` and the general `binaryColorings_complete` theorem |
| Chromatic number exactly 3 | `liGraph_chromatic_number`: proper 3-coloring and no `m`-coloring for any `m < 3` |
| Every edge deletion has chromatic number exactly 2 | `liGraph_deleted_edge_chromatic_two` |
| Every vertex deletion has chromatic number exactly 2 | `liGraph_deleted_vertex_chromatic_two` |
| Every proper subhypergraph is 2-colorable | `liGraph_all_proper_subgraphs`, with arbitrary surviving vertex predicate and edge sublist |
| Minimum degree exactly 7 | `liGraph_minimum_degree` and `liGraph_degrees` |

Coloring is **weak** hypergraph coloring: each triple must contain two
differently colored vertices. It is not rainbow/strong coloring. For a vertex
deletion, the color on the removed vertex is irrelevant: the quantified total
function restricts to a coloring of the surviving vertices. The auxiliary
Python test separately enumerates colorings on the eight surviving vertices.

The finite checks use Lean's kernel-reduced `decide`. The completeness lemma
proves that enumeration covers **every** function `Fin n → Bool`; an unproved
claim that a mask search is exhaustive is not assumed. The main theorem has no
unproved mathematical premises and no placeholder proof terms.

## Scope and prize status

This proves the full chromatic question explicitly stated in the current JSP
catalog and Li's Theorem 1.2. It does **not** prove the separate transversal
number (`tau`-criticality) theorem, does not formalize every result in Li's paper,
and does not resolve competing priority claims.

See [VERIFICATION.md](VERIFICATION.md) for the actual verification record.
Repository CI and local verification are not prize approval. Submission,
statement review, safe-toolchain review, attribution, priority, identity checks,
award assessment, and payment remain separate official decisions. No private
contact details, identity documents, or payment addresses are included here.
