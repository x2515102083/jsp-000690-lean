import JSP690
import Transversal

/-!
# Both meanings of 3-critical in Erdos 834

This integrates the existing chromatic construction with the separately written
transversal degree argument. Mathematical credit and prior full formalizations
are disclosed in ATTRIBUTION.md and TRANSVERSAL_ATTRIBUTION.md.
SPDX-License-Identifier: MIT
-/

namespace JSP690Complete

/-- The two opposite answers, together with sharpness of the transversal bound.
All vertex counts in the negative clause are quantified without an upper bound. -/
theorem erdos834_both :
    (∃ n : Nat, ∃ G : JSP690.Hypergraph n,
      JSP690.SimpleThreeUniform G ∧ JSP690.ChromaticCriticalThree G ∧
      JSP690.AllProperSubgraphsTwoColorable G ∧
      (∀ v : Fin n, 7 ≤ JSP690.degree G v) ∧
      (∃ v : Fin n, JSP690.degree G v = 7)) ∧
    (¬ ∃ (n : Nat) (H : Finset (Finset (Fin n))),
      (∀ e ∈ H, e.card = 3) ∧ JSP690Transversal.TauCriticalThree H ∧
      (∀ v : Fin n, 7 ≤ JSP690Transversal.degree H v)) ∧
    (∃ (n : Nat) (H : Finset (Finset (Fin n))),
      (∀ e ∈ H, e.card = 3) ∧ JSP690Transversal.TauCriticalThree H ∧
      (∀ v : Fin n, JSP690Transversal.degree H v = 6)) :=
  ⟨JSP690.jsp000690, JSP690Transversal.no_minimum_degree_seven,
    JSP690Transversal.degree_bound_sharp⟩

/-- The pointwise strengthening supplied by the link argument. -/
theorem every_transversal_degree_le_six {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) (hu : ∀ e ∈ H, e.card = 3)
    (hc : JSP690Transversal.TauCriticalThree H) (v : V) :
    JSP690Transversal.degree H v ≤ 6 :=
  JSP690Transversal.degree_le_six hu hc v

end JSP690Complete
