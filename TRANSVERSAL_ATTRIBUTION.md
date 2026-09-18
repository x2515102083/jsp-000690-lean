# September 18, 2026 extension: provenance and overlap

The original mathematical problem and both answers are credited to their
published sources, in particular Ruiliang Li, arXiv:2512.24850v1.
The link-degree bound is an elementary instance of classical set-pairs
reasoning; no first mathematical discovery is claimed for it.

The new Lean files `Transversal.lean` and `Complete690.lean`, the new verification
script and the extension documentation were prepared with OpenAI ChatGPT
assistance at the request of the public GitHub account `x2515102083`.
The existing chromatic implementation is reused with its original notices.
The public account commissioned and publishes this work; this does not assert
manual human authorship of every line or a verified legal recipient identity.

## Prior complete work

The source
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos834.lean
already formalizes BOTH interpretations and credits Codex / GPT-5.6 Sol.
Its transversal argument proves at most ten edges with a Bollobas two-families
inequality, at least five vertices, and the existence of a degree-at-most-six
vertex by averaging. That earlier full scope and priority are preserved.

The present separately written implementation proves a pointwise bound on
EVERY degree via a rank-two link argument. It avoids importing the earlier
formalization or its general two-families proof. This is a different
implementation and a stronger displayed degree conclusion than the inspected
prior endpoint, not a certification that the degree fact is mathematically new
or has never been formalized elsewhere.

A search and excerpts of the prior source were read during comparison after
commit b035d6a7724b0d0233becb4808950fbb73b79dec (the first published local
transversal development source). Independence from all prior formalization
ideas is not asserted. The earlier chromatic-only disclosures in ATTRIBUTION.md
continue to apply, including the source consulted through issue #15.
Additional chromatic submissions inspected include #845, #879 and #1097.
The last of these describes a different 21-edge regular witness; we do not
claim that optimization or copy that construction.

## Requested recognition and verification boundary

This extension may be reviewed as a later pointwise-degree implementation and
full-problem integration. It is NOT first full formalization, first solution,
a mathematical-solver claim, a guaranteed joint award, or entitlement to any
percentage of a prize. Earlier authors and timestamps must retain their credit.
The account has a direct interest in recognition; the authoring assistant and
contributor-run CI are not independent human reviewers. The committee decides
whether this incremental contribution qualifies for any recognition at all.

No private contact, identity document or payment detail is supplied. No official
candidate, eligibility, recipient or award record is changed by this package.
The development history includes failed compilation attempts. These are not
successful verification evidence; use only a completed successful run for the
exact selected source commit.
