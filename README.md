# JSP-000690 / Erdős 834: both meanings of 3-critical

This version resolves the degree-seven existence question under **both** standard meanings of criticality. It upgrades the same account's chromatic-only submission in [awards PR #842](https://github.com/TheJustinSunPrize/awards/pull/842); it is not a second submission for the same work.

| Meaning of criticality | Formal conclusion |
| --- | --- |
| Weak chromatic number exactly 3, dropping after deleting any edge or vertex | Yes: Li's 9-vertex, 22-edge construction, minimum degree exactly 7. All proper subhypergraphs are also proved 2-colorable. |
| Transversal number exactly 3, dropping after deleting any edge | No: **every vertex** has degree at most 6, for arbitrary finite simple 3-uniform hypergraphs. The bound is attained by the complete 3-graph on 5 vertices. |

**Main theorem:** `JSP690Complete.complete_resolution`, in [Complete.lean](Complete.lean). It states both answers separately and adds sharpness of the transversal bound. There are no extra mathematical hypotheses in this combined theorem. The two meanings are not identified with each other.

This is complete for the original minimum-degree-seven existence question, not every theorem in the source paper: the separate universal bound of ten edges is not asserted here. The current prize catalog explicitly uses the chromatic wording; the transversal supplement also covers the alternative reading raised in [scope issue #882](https://github.com/TheJustinSunPrize/awards/issues/882).

## Sources and contribution

The mathematical resolution is attributed to **Ruiliang Li**, [arXiv:2512.24850v1](https://arxiv.org/abs/2512.24850v1). The transversal argument uses the classical (2,2) set-pairs bound. No new mathematical discovery is claimed.

`JSP690.lean` is **byte-for-byte unchanged** from this repository's original commit `05e214a2d112513abd5c4a43fa7e40358457de82`. It now compiles on pinned stable Lean 4.32.1, instead of the original release candidate.

The new `Transversal.lean` gives a separately written elementary proof of the set-pairs bound, by stars and two disjoint pairs, followed by the universal pointwise degree theorem. `Complete.lean` joins it to the existing chromatic proof. See [the mathematical proof and statement correspondence](PROOF.md) and [attribution, AI assistance and prior work](ATTRIBUTION.md).

**An earlier complete formalization covering both readings already exists** in `plby/lean-proofs`, commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, `src/latest/ErdosProblems/Erdos834.lean`. It was consulted during scope review. This upgrade is not a first-formalization claim and does not displace any earlier author or timestamp. That source is neither imported nor redistributed here.

## Reproduction

Required: Git, Python 3.11 or newer, and the exact Lean toolchain in `lean-toolchain`:

- Lean `v4.32.1`, release commit `f054605aea4b840552cca2e725580bffd1e1b704`.
- Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`.
- All nine dependency revisions are fixed in the committed manifest.

From a clean checkout of the selected branch and commit:

```sh
python3 bootstrap.py
lake exe cache get .lake/packages/mathlib/Mathlib/Data/Finset/Powerset.lean .lake/packages/mathlib/Mathlib/Data/Finset/Prod.lean .lake/packages/mathlib/Mathlib/Data/Fintype/Powerset.lean
python3 scripts/verify.py
```

On Windows use `python` in place of `python3`. The bootstrap script refuses to overwrite an existing dependency checkout at a different revision or with modified tracked source. It does not run `lake update`.

The verifier runs `lake build`, fresh warning-as-error elaboration of all three local modules, a fail-closed 12-root axiom audit, and `leanchecker --verbose JSP690 Transversal Complete`. It then runs ten axiom-parser regression tests and the auxiliary chromatic and transversal Python checks. Audited source hashes and lockfiles must remain unchanged.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by the audit. There is no `sorry`, `admit`, project mathematical axiom, `unsafe`, or `native_decide` in the four audited Lean files. Concrete finite facts use ordinary kernel-checked `decide`.

## Verification boundary

See [VERIFICATION.md](VERIFICATION.md). The verifier produces timestamped commands, exit codes, source hashes and logs under `verification-output/`. The checked commit is recorded by CI. A successful contributor workflow is not organizer-designated verification or an award decision.

Leanchecker replays the local declarations with Lean's own kernel and the pinned imported compiled libraries. It is **not** a separate kernel implementation, independent human review, or a fresh source rebuild/replay of all Mathlib. The auxiliary exhaustive checks are not proof premises.

Submission, priority, any recognition, recipient identity and payment remain for the prize process. No public claim email, identity declaration, award status or payment request is created by this repository update.
