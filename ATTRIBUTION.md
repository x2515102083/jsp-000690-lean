# Attribution and prior-work disclosure

## Mathematical source

Ruiliang Li, **On an Erdős–Lovász problem: 3-critical 3-graphs of minimum
degree 7**, arXiv:2512.24850v1 (2025).

- [Versioned source and metadata](https://arxiv.org/abs/2512.24850v1)
- [Theorem 1.2, Theorem 4.1 and equation (5)](https://arxiv.org/html/2512.24850v1#S4)
- [Original problem and the two distinct interpretations](https://www.erdosproblems.com/834)
- [Prize catalog, JSP-000690](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000690)

The edge set and the three-coloring are mathematical data from Li's construction.
The problem and the construction are not claimed as discoveries of this project.
The article is cited as a preprint; no peer-reviewed publication status is asserted.
The paper's integer vertex labels are reduced by one in the Lean representation.

## This repository

Account responsible for commissioning, publishing, and maintaining this
AI-assisted formalization: **x2515102083**.

Lean code, general enumeration-completeness argument, arbitrary-subhypergraph
bridge, verification scripts and documentation were produced using **OpenAI
Codex**, acting at that account holder's request. This is not a representation
that the account holder manually wrote every proof step. No separate human
expert review or independently certified verifier role is claimed. The relation
between the applicant, the AI-assisted work and any eventual recipient role is
for the maintainers to verify.

The implementation was written in this repository from the mathematical
construction. A prior public formalization was read during feasibility review,
so **independence from all prior formalization ideas is not asserted**. The
general recursive enumeration, proof of completeness, exact chromatic-number
statements, arbitrary proper-subhypergraph argument, and executable checks are
documented so the contribution can be assessed without relying on ownership
alone. This repository is not a mirror of another proof repository.

## Earlier work and overlapping submissions

Earlier public submissions were found before publication of this repository.
They must retain their authorship and earlier timestamps. In particular:

- [Issue #15](https://github.com/TheJustinSunPrize/awards/issues/15) already
  contains a complete `Std`-only formalization. Its source and explanation were
  consulted during feasibility review.
- [Issue #157](https://github.com/TheJustinSunPrize/awards/issues/157) describes
  `aqin1996/jsp-000690-lean`.
- [Issue #697](https://github.com/TheJustinSunPrize/awards/issues/697) describes
  `homelymole95/jsp-000690-chromatic-lean`.
- Earlier direct catalog/proof PRs found by a separate PR search include
  [#21](https://github.com/TheJustinSunPrize/awards/pull/21),
  [#35](https://github.com/TheJustinSunPrize/awards/pull/35),
  [#39](https://github.com/TheJustinSunPrize/awards/pull/39),
  [#427](https://github.com/TheJustinSunPrize/awards/pull/427),
  [#717](https://github.com/TheJustinSunPrize/awards/pull/717),
  [#737](https://github.com/TheJustinSunPrize/awards/pull/737),
  [#747](https://github.com/TheJustinSunPrize/awards/pull/747),
  [#794](https://github.com/TheJustinSunPrize/awards/pull/794), and
  [#823](https://github.com/TheJustinSunPrize/awards/pull/823).

This list is a disclosure, not a certification of those proofs or an exhaustive
priority registry. The present author account is a later submitter with an
interest in possible recognition. There is **no claim to first mathematical
solution, first formalization, guaranteed joint-award eligibility, or a fixed
payment amount**. Whether another implementation has reward value is solely a
maintainer/committee decision.

Earlier `JSP-000921` work under the same account is a different contribution and
is not used to claim completion of that separate problem here.
