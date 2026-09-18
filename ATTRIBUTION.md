# Attribution, AI assistance and prior work

## Mathematical sources

Ruiliang Li, *On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7*, [arXiv:2512.24850v1](https://arxiv.org/abs/2512.24850v1), dated December 19, 2025. See Definitions 2.1/2.3, Theorems 1.1/1.2, and Theorem 4.1 with equation (5). This is cited as a preprint; no separate publication or referee status is asserted.

Li's 9-vertex, 22-edge construction and its three-coloring are used by the existing chromatic proof. The integer vertex labels are reduced by one. The negative transversal answer and its sharp complete-five example are also established in that paper. Our pointwise degree proof is an application of the classical (2,2) case of Bollobás's set-pairs inequality, not a new mathematical discovery.

The present development does not assert or formalize Li's separate ten-edge bound. Its degree theorem suffices for the complete original degree-seven question.

## Account and AI assistance

The public account responsible for commissioning, publishing and maintaining this work is **x2515102083**. This does not establish a verified legal recipient identity or unaided manual authorship.

The original chromatic module and scripts were produced with **OpenAI Codex** assistance at the account holder's request. The September 18, 2026 supplement, its elementary set-pairs argument, Lean code, integration and checking were produced with **ChatGPT** assistance. All machine checks in this package are contributor-run. No independent human expert or separately implemented kernel verifier is claimed.

`JSP690.lean` remains byte-for-byte equal to the original source in this repository at `05e214a2d112513abd5c4a43fa7e40358457de82` (Git blob `c9a9d156efc65757a77babb2a0ad33e2b0923771`). That existing work is reused, not presented as newly written in the supplement.

The new contribution of this version is `Transversal.lean`, `Complete.lean`, the stable-toolchain integration and reproducible audit. In contrast with a general permutation-counting proof, the new set-pairs implementation uses a three-member star bound and a two-disjoint-pairs case. It is separately written and neither imports nor re-exports the earlier Erdős 834 proof.

## Earlier and overlapping work

An **earlier complete proof of both interpretations** exists in [plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos834.lean). Its notices name Ruiliang Li for the mathematics and Codex / GPT-5.6 Sol for formalization. Its source was inspected during scope review. Independence from all prior mathematical or formalization ideas is therefore **not** asserted. It is not copied, vendored or imported into this package.

Earlier overlap disclosed for the original chromatic-only version remains relevant: awards issues [#15](https://github.com/TheJustinSunPrize/awards/issues/15), [#157](https://github.com/TheJustinSunPrize/awards/issues/157), [#697](https://github.com/TheJustinSunPrize/awards/issues/697), and PRs #21, #35, #39, #427, #717, #737, #747, #794 and #823. In particular, the Std-only source in issue #15 was read during the original feasibility assessment. The original disclosures remain available at the parent commit. Later scope discussion #882 and the associated #879/#880 submission are separate contributors' records.

This list is not an exhaustive priority registry or a certification of those submissions. Prior authors and public timestamps retain their credit. **No first mathematical solution, first formalization, first two-reading proof, guaranteed joint award, automatic formalizer share or payment amount is claimed.** This account is a later contributor with an interest in possible recognition; the committee must assess whether this incremental completeness upgrade merits any recognition at all.

Existing awards PR #842 is updated for this same implementation; no duplicate PR is needed. The account's separate Erdős 339, Erdős 549, Erdős 287 finite-certificate and earlier JSP-000921 work is not used to claim a new solution here.

## Licensing and identity

New project files are MIT-licensed under this repository's existing LICENSE. The unchanged chromatic source retains its notice. Mathlib, Lean and transitive dependencies retain their respective upstream licenses and are not redistributed in the source submission. The public proof source is distinct from a confirmed prize recipient. No private identity, contact or payment material belongs in this record.
