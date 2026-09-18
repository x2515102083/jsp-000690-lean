import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# The transversal interpretation of Erdos 834 / JSP-000690

Mathematical context: Ruiliang Li, arXiv:2512.24850v1, Theorem 1.1,
and classical set-pairs methods. No new mathematical-solver claim.
Formalization: x2515102083 with OpenAI ChatGPT assistance, 2026.
SPDX-License-Identifier: MIT
-/

namespace JSP690Transversal

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
variable {V : Type*} [DecidableEq V]

def Hits (A B : Finset V) : Prop := ∃ x, x ∈ A ∧ x ∈ B

def Covers (H : Finset (Finset V)) (T : Finset V) : Prop :=
  ∀ e ∈ H, Hits e T

def degree (H : Finset (Finset V)) (v : V) : Nat :=
  (H.filter (fun e => v ∈ e)).card

/-- Exact transversal number without an infimum convention. -/
def TauExactly (H : Finset (Finset V)) (k : Nat) : Prop :=
  (∃ T : Finset V, T.card = k ∧ Covers H T) ∧
  ∀ T : Finset V, T.card < k → ¬ Covers H T

/-- Transversal edge-criticality, not chromatic criticality. -/
def TauCriticalThree (H : Finset (Finset V)) : Prop :=
  TauExactly H 3 ∧ ∀ e ∈ H, TauExactly (H.erase e) 2

def PairCritical (E : Finset (Finset V)) : Prop :=
  (∀ e ∈ E, e.card = 2) ∧
  ∀ e ∈ E, ∃ B : Finset V, B.card ≤ 2 ∧ Disjoint e B ∧
    ∀ f ∈ E, f ≠ e → Hits f B

lemma pair_at_vertex {e : Finset V} {x : V} (he : e.card = 2) (hx : x ∈ e) :
    ∃ y, y ≠ x ∧ e = {x, y} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, Ne.symm hab, rfl⟩
  · exact ⟨a, hab, by ext z; simp [or_comm]⟩

lemma pair_eq_of_members {e : Finset V} {x y : V}
    (he : e.card = 2) (hxy : x ≠ y) (hx : x ∈ e) (hy : y ∈ e) : e = {x, y} := by
  obtain ⟨z, hzx, rfl⟩ := pair_at_vertex he hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with hy | hy
  · exact (hxy hy.symm).elim
  · subst z; rfl

lemma pair_degree_le_three {E : Finset (Finset V)} (hE : PairCritical E) (x : V) :
    degree E x ≤ 3 := by
  unfold degree
  by_cases hn : (E.filter (fun e => x ∈ e)).Nonempty
  · obtain ⟨e, he⟩ := hn
    obtain ⟨heE, hxe⟩ := Finset.mem_filter.mp he
    obtain ⟨B, hB, hd, hc⟩ := hE.2 e heE
    have hxB : x ∉ B := fun hx => Finset.disjoint_left.mp hd hxe hx
    have hsub : E.filter (fun f => x ∈ f) ⊆ insert e (B.image (fun y => ({x,y} : Finset V))) := by
      intro f hf
      obtain ⟨hfE, hxf⟩ := Finset.mem_filter.mp hf
      by_cases hfe : f = e
      · simp [hfe]
      · obtain ⟨y, hyf, hyB⟩ := hc f hfE hfe
        have hxy : x ≠ y := by intro h; subst y; exact hxB hyB
        have hfxy := pair_eq_of_members (hE.1 f hfE) hxy hxf hyf
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨y, hyB, hfxy.symm⟩
    calc
      _ ≤ (insert e (B.image (fun y => ({x,y} : Finset V)))).card := Finset.card_le_card hsub
      _ ≤ (B.image (fun y => ({x,y} : Finset V))).card + 1 := Finset.card_insert_le _ _
      _ ≤ B.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ 3 := by omega
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hz]

lemma pair_card_le_five_of_degree_le_two {E : Finset (Finset V)}
    (hE : PairCritical E) (hdeg : ∀ x, degree E x ≤ 2) : E.card ≤ 5 := by
  by_cases hn : E.Nonempty
  · obtain ⟨e, he⟩ := hn
    obtain ⟨B, hB, _, hc⟩ := hE.2 e he
    have hsub : E.erase e ⊆ B.biUnion (fun x => E.filter (fun f => x ∈ f)) := by
      intro f hf
      obtain ⟨hfe, hfE⟩ := Finset.mem_erase.mp hf
      obtain ⟨x, hxf, hxB⟩ := hc f hfE hfe
      exact Finset.mem_biUnion.mpr ⟨x, hxB, Finset.mem_filter.mpr ⟨hfE, hxf⟩⟩
    have hbound : (E.erase e).card ≤ 4 := by
      calc
        _ ≤ (B.biUnion (fun x => E.filter (fun f => x ∈ f))).card := Finset.card_le_card hsub
        _ ≤ ∑ x ∈ B, (E.filter (fun f => x ∈ f)).card := Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ B, 2 := Finset.sum_le_sum (fun x _ => hdeg x)
        _ = B.card * 2 := by simp
        _ ≤ 4 := by omega
    have hcard := Finset.card_erase_of_mem he
    have hpos := Finset.card_pos.mpr hn
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

lemma forced_pair_witness {E : Finset (Finset V)} {x a b c : V}
    (hE : PairCritical E)
    (ha : ({x,a} : Finset V) ∈ E) (hb : ({x,b} : Finset V) ∈ E)
    (hc : ({x,c} : Finset V) ∈ E)
    (hab : ({x,a} : Finset V) ≠ {x,b})
    (hac : ({x,a} : Finset V) ≠ {x,c}) (hbc : b ≠ c) :
    ∀ f ∈ E, f ≠ {x,a} → Hits f {b,c} := by
  obtain ⟨B, hB, hd, hcover⟩ := hE.2 _ ha
  have hxB : x ∉ B := fun hx => Finset.disjoint_left.mp hd (by simp) hx
  have hbB : b ∈ B := by
    obtain ⟨z, hz, hzB⟩ := hcover _ hb (Ne.symm hab)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (hxB hzB).elim
    · exact hzB
  have hcB : c ∈ B := by
    obtain ⟨z, hz, hzB⟩ := hcover _ hc (Ne.symm hac)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (hxB hzB).elim
    · exact hzB
  have hsub : ({b,c} : Finset V) ⊆ B := by simp [hbB, hcB]
  have heq : B = {b,c} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    simpa [hbc] using hB
  simpa [heq] using hcover

lemma meets_three_pairs {f : Finset V} {a b c : V} (hf : f.card = 2)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : Hits f {b,c}) (h2 : Hits f {a,c}) (h3 : Hits f {a,b}) :
    f = {a,b} ∨ f = {a,c} ∨ f = {b,c} := by
  have h1' : b ∈ f ∨ c ∈ f := by
    simpa [Hits, and_or_left, exists_or] using h1
  have h2' : a ∈ f ∨ c ∈ f := by
    simpa [Hits, and_or_left, exists_or] using h2
  have h3' : a ∈ f ∨ b ∈ f := by
    simpa [Hits, and_or_left, exists_or] using h3
  by_cases ha : a ∈ f
  · by_cases hb : b ∈ f
    · exact Or.inl (pair_eq_of_members hf hab ha hb)
    · exact Or.inr (Or.inl (pair_eq_of_members hf hac ha (h1'.resolve_left hb)))
  · exact Or.inr (Or.inr (pair_eq_of_members hf hbc
      (h3'.resolve_left ha) (h2'.resolve_left ha)))

/-- Elementary rank-two case of the set-pairs bound. -/
theorem pair_card_le_six {E : Finset (Finset V)} (hE : PairCritical E) : E.card ≤ 6 := by
  by_cases hdeg : ∀ x, degree E x ≤ 2
  · exact (pair_card_le_five_of_degree_le_two hE hdeg).trans (by decide)
  · push_neg at hdeg
    obtain ⟨x, hx⟩ := hdeg
    have hx3 : degree E x = 3 := by have := pair_degree_le_three hE x; omega
    obtain ⟨e1, e2, e3, h12, h13, h23, heq⟩ := Finset.card_eq_three.mp hx3
    have hmem1 : e1 ∈ E.filter (fun e => x ∈ e) := by rw [heq]; simp
    have hmem2 : e2 ∈ E.filter (fun e => x ∈ e) := by rw [heq]; simp
    have hmem3 : e3 ∈ E.filter (fun e => x ∈ e) := by rw [heq]; simp
    obtain ⟨he1, hx1⟩ := Finset.mem_filter.mp hmem1
    obtain ⟨he2, hx2⟩ := Finset.mem_filter.mp hmem2
    obtain ⟨he3, hx3'⟩ := Finset.mem_filter.mp hmem3
    obtain ⟨a, hax, rfl⟩ := pair_at_vertex (hE.1 e1 he1) hx1
    obtain ⟨b, hbx, rfl⟩ := pair_at_vertex (hE.1 e2 he2) hx2
    obtain ⟨c, hcx, rfl⟩ := pair_at_vertex (hE.1 e3 he3) hx3'
    have hab : a ≠ b := by intro h; subst b; exact h12 rfl
    have hac : a ≠ c := by intro h; subst c; exact h13 rfl
    have hbc : b ≠ c := by intro h; subst c; exact h23 rfl
    have hw1 := forced_pair_witness hE he1 he2 he3 h12 h13 hbc
    have hw2 := forced_pair_witness hE he2 he1 he3 (Ne.symm h12) h23 hac
    have hw3 := forced_pair_witness hE he3 he1 he2 (Ne.symm h13) (Ne.symm h23) hab
    have hsub : E ⊆ ({ {x,a}, {x,b}, {x,c}, {a,b}, {a,c}, {b,c} } : Finset (Finset V)) := by
      intro f hf
      by_cases hfx : x ∈ f
      · have hfm : f ∈ E.filter (fun e => x ∈ e) := Finset.mem_filter.mpr ⟨hf, hfx⟩
        rw [heq] at hfm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hfm ⊢
        tauto
      · have hn1 : f ≠ {x,a} := by intro h; subst f; exact hfx (by simp)
        have hn2 : f ≠ {x,b} := by intro h; subst f; exact hfx (by simp)
        have hn3 : f ≠ {x,c} := by intro h; subst f; exact hfx (by simp)
        have hp := meets_three_pairs (hE.1 f hf) hab hac hbc
          (hw1 f hf hn1) (hw2 f hf hn2) (hw3 f hf hn3)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
    calc
      _ ≤ ({ {x,a}, {x,b}, {x,c}, {a,b}, {a,c}, {b,c} } : Finset (Finset V)).card := Finset.card_le_card hsub
      _ ≤ 6 := by
        exact le_trans (Finset.card_insert_le _ _) (by
          have h1 := Finset.card_insert_le ({x,b} : Finset V) ({ {x,c}, {a,b}, {a,c}, {b,c} } : Finset (Finset V))
          have h2 := Finset.card_insert_le ({x,c} : Finset V) ({ {a,b}, {a,c}, {b,c} } : Finset (Finset V))
          have h3 := Finset.card_insert_le ({a,b} : Finset V) ({ {a,c}, {b,c} } : Finset (Finset V))
          have h4 := Finset.card_insert_le ({a,c} : Finset V) ({ {b,c} } : Finset (Finset V))
          simp only [Finset.card_singleton] at h4
          omega)

lemma deletion_cover_disjoint {H : Finset (Finset V)}
    (hno : ∀ T : Finset V, T.card ≤ 2 → ¬ Covers H T)
    {e B : Finset V} (hB : B.card ≤ 2) (hc : Covers (H.erase e) B) : Disjoint e B := by
  apply Finset.disjoint_left.mpr
  intro x hxe hxB
  apply hno B hB
  intro f hf
  by_cases hfe : f = e
  · subst f; exact ⟨x, hxe, hxB⟩
  · exact hc f (Finset.mem_erase.mpr ⟨hfe, hf⟩)

def link (H : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (H.filter (fun e => v ∈ e)).image (fun e => e.erase v)

lemma erase_injective_incident {e f : Finset V} {v : V}
    (he : v ∈ e) (hf : v ∈ f) (h : e.erase v = f.erase v) : e = f := by
  have := congrArg (insert v) h
  simpa [Finset.insert_erase he, Finset.insert_erase hf] using this

lemma link_card (H : Finset (Finset V)) (v : V) : (link H v).card = degree H v := by
  unfold link degree
  apply Finset.card_image_iff.mpr
  intro e he f hf hef
  exact erase_injective_incident (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2 hef

lemma link_pair_critical {H : Finset (Finset V)}
    (hu : ∀ e ∈ H, e.card = 3)
    (hno : ∀ T : Finset V, T.card ≤ 2 → ¬ Covers H T)
    (hdel : ∀ e ∈ H, ∃ B : Finset V, B.card ≤ 2 ∧ Covers (H.erase e) B)
    (v : V) : PairCritical (link H v) := by
  constructor
  · intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨heH, hve⟩ := Finset.mem_filter.mp he
    rw [Finset.card_erase_of_mem hve, hu e heH]
  · intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨heH, hve⟩ := Finset.mem_filter.mp he
    obtain ⟨B, hB, hc⟩ := hdel e heH
    have hd := deletion_cover_disjoint hno hB hc
    refine ⟨B, hB, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro x hx hxB
      exact Finset.disjoint_left.mp hd (Finset.mem_erase.mp hx).2 hxB
    · intro b hb hne
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hfH, hvf⟩ := Finset.mem_filter.mp hf
      have hfe : f ≠ e := by intro h; subst f; exact hne rfl
      obtain ⟨x, hxf, hxB⟩ := hc f (Finset.mem_erase.mpr ⟨hfe, hfH⟩)
      have hxv : x ≠ v := by
        intro h; subst x
        exact Finset.disjoint_left.mp hd hve hxB
      exact ⟨x, Finset.mem_erase.mpr ⟨hxv, hxf⟩, hxB⟩

/-- Every vertex has degree at most six, not merely some vertex. -/
theorem degree_le_six {H : Finset (Finset V)}
    (hu : ∀ e ∈ H, e.card = 3) (hc : TauCriticalThree H) (v : V) : degree H v ≤ 6 := by
  have hno : ∀ T : Finset V, T.card ≤ 2 → ¬ Covers H T := by
    intro T hT
    exact hc.1.2 T (by omega)
  have hdel : ∀ e ∈ H, ∃ B : Finset V, B.card ≤ 2 ∧ Covers (H.erase e) B := by
    intro e he
    obtain ⟨B, hB, hb⟩ := (hc.2 e he).1
    exact ⟨B, by omega, hb⟩
  rw [← link_card]
  exact pair_card_le_six (link_pair_critical hu hno hdel v)

/-- Full negative answer, with arbitrary finite vertex count. -/
theorem no_minimum_degree_seven :
    ¬ ∃ (n : Nat) (H : Finset (Finset (Fin n))),
      (∀ e ∈ H, e.card = 3) ∧ TauCriticalThree H ∧
      (∀ v : Fin n, 7 ≤ degree H v) := by
  rintro ⟨n, H, hu, hc, hdeg⟩
  obtain ⟨T, hT, _⟩ := hc.1.1
  have hn : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, _⟩ := hn
  have h6 := degree_le_six hu hc v
  have h7 := hdeg v
  omega

def completeFive : Finset (Finset (Fin 5)) :=
  (Finset.univ : Finset (Fin 5)).powersetCard 3

theorem completeFive_uniform : ∀ e ∈ completeFive, e.card = 3 := by
  intro e he
  exact (Finset.mem_powersetCard.mp he).2

theorem completeFive_critical : TauCriticalThree completeFive := by
  unfold TauCriticalThree TauExactly Covers Hits completeFive
  decide

theorem completeFive_degrees : ∀ v : Fin 5, degree completeFive v = 6 := by
  unfold degree completeFive
  decide

theorem degree_bound_sharp :
    ∃ (n : Nat) (H : Finset (Finset (Fin n))),
      (∀ e ∈ H, e.card = 3) ∧ TauCriticalThree H ∧
      (∀ v : Fin n, degree H v = 6) :=
  ⟨5, completeFive, completeFive_uniform, completeFive_critical, completeFive_degrees⟩

#print axioms pair_card_le_six
#print axioms degree_le_six
#print axioms no_minimum_degree_seven
#print axioms degree_bound_sharp

end JSP690Transversal
