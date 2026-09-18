# JSP-000690 / Erdos 834: both interpretations

This branch extends the earlier chromatic-only package. It does not change the
catalog's stated problem or assert an award. The combined target is
`JSP690Complete.erdos834_both` in `Complete690.lean`.

## Results and scope

The chromatic clause supplies Li's 9-vertex, 22-edge example: a simple
three-uniform hypergraph with weak chromatic number exactly three, every proper
subhypergraph two-colourable, and attained minimum degree seven. The original
`JSP690.lean` implementation is retained.

The transversal clause proves, for arbitrary finite hypergraphs satisfying
`tau(H)=3` and `tau(H-e)=2` for every edge, that **every vertex has degree at most
six**. In particular, minimum degree seven is impossible at every vertex count.
A separately checked complete three-graph on five vertices attains degree six.
This is a complete negative answer, not a bounded search. The pointwise theorem
`JSP690Transversal.degree_le_six` even allows an arbitrary ambient type.

The source question has two non-equivalent meanings of criticality, giving
opposite answers. See [statement mapping](STATEMENT.md), the original problem
at https://www.erdosproblems.com/834 and Li's paper
https://arxiv.org/html/2512.24850v1 . This package is not a formalization of every
theorem in that paper: in particular it does not claim its separate ten-edge
bound as a new formal theorem.

## Build and verification

Lean `4.34.0`, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The manifest pins
all nine dependencies. Install the toolchain in `lean-toolchain`, then run:

```sh
lake exe cache get Mathlib.Data.Finset.Powerset Mathlib.Tactic
python3 scripts/verify_complete.py
```

`lake build` builds all three modules. The verification script freshly
elaborates their sources with warnings treated as errors, inventories every
local theorem/lemma, checks each complete axiom closure against
`propext`, `Classical.choice`, `Quot.sound`, prints the definitions and main
statement types, replays each local module using bundled `leanchecker`, runs
both auxiliary cross-checks and the audit regression tests, and rejects source
or lockfile changes. A missing target report is a failure. Finite certificates
use ordinary `decide`, not native evaluation.

The `Verify both interpretations` workflow runs this procedure on a fresh
checkout. An actual successful run for the selected commit is required;
the existence of workflow code or this README is not proof that a run passed.
Actual logs and a JSON receipt are produced under `evidence-complete/` and in
the workflow artifact. `VERIFICATION.md` is the historical chromatic-only
receipt for the old commit, not evidence for this extension.

The same Lean kernel is used for elaboration and replay. Mathlib's compiled
cache and imported declarations are reused. This is not a separate kernel
implementation, an all-dependencies source rebuild, independent human review,
or organizer-designated verification.

## Attribution and overlap

Mathematical resolution: Ruiliang Li. The elementary link argument is related
to classical set-pairs bounds; no new mathematical discovery is claimed.
Public contributor account: `x2515102083`, with OpenAI Codex/ChatGPT assistance.
See [original attribution](ATTRIBUTION.md) and
[extension attribution and comparison](TRANSVERSAL_ATTRIBUTION.md).

**A prior plby formalization already covers both interpretations.** This
extension is not the first complete formalization. Its new implementation
component in this repository is the pointwise link-degree argument and
integration, not ownership of earlier results. Source excerpts of the prior
proof were inspected for comparison after the first local development commit;
that proof is not imported or copied into this package.

No independent human reviewer, verified recipient identity, first-publication
priority, award tier, prize amount or entitlement to payment is asserted.
Existing catalog PR: TheJustinSunPrize/awards#842; updates should reuse it.
