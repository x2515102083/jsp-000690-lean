/-
SPDX-License-Identifier: MIT
Prepared for public account x2515102083 with ChatGPT assistance, 2026-09-18.

An elementary (2,2) set-pairs argument and the sharp pointwise degree bound
for transversal-three-critical simple 3-uniform hypergraphs.
The mathematical bound is classical; see ATTRIBUTION.md. This proof does
not import or re-export the earlier Erdős 834 formalization.
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Powerset

namespace JSP690Transversal

open Finset

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq α] in
/-- The two sides of a finite cross-intersecting system are distinct. -/
lemma left_injective {S : Finset ι} {A B : ι → Finset α}
    (own : ∀ i ∈ S, Disjoint (A i) (B i))
    (cross : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬Disjoint (A i) (B j)) :
    Set.InjOn A (S : Set ι) := by
  intro i hi j hj hij
  by_contra hne
  have hc := cross i hi j hj hne
  exact hc (hij ▸ own j hj)

omit [DecidableEq α] in
lemma right_injective {S : Finset ι} {A B : ι → Finset α}
    (own : ∀ i ∈ S, Disjoint (A i) (B i))
    (cross : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬Disjoint (A i) (B j)) :
    Set.InjOn B (S : Set ι) := by
  intro i hi j hj hij
  by_contra hne
  exact (cross i hi j hj hne) (hij ▸ own i hi)

/-- If a two-element set contains distinct `a,b`, it is exactly `{a,b}`. -/
lemma pair_eq_of_mem {s : Finset α} {a b : α} (hs : s.card ≤ 2)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : s = {a,b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact h ▸ ha
    · exact (Finset.mem_singleton.mp h) ▸ hb
  · simpa [hab] using hs

/-- A star among the left pairs has at most three members. -/
lemma star_card_le_three {S : Finset ι} {A B : ι → Finset α}
    (hA : ∀ i ∈ S, (A i).card = 2)
    (hB : ∀ i ∈ S, (B i).card ≤ 2)
    (own : ∀ i ∈ S, Disjoint (A i) (B i))
    (cross : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬Disjoint (A i) (B j))
    (a : α) : (S.filter (fun i => a ∈ A i)).card ≤ 3 := by
  let T := S.filter (fun i => a ∈ A i)
  change T.card ≤ 3
  by_cases ht : T.Nonempty
  · obtain ⟨i, hi⟩ := ht
    have his : i ∈ S := (Finset.mem_filter.mp hi).1
    have hai : a ∈ A i := (Finset.mem_filter.mp hi).2
    have han : a ∉ B i := Finset.disjoint_left.mp (own i his) hai
    have hsub : (T.erase i).image A ⊆ (B i).image (fun b => ({a,b} : Finset α)) := by
      intro s hs
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hjt : j ∈ T := (Finset.mem_erase.mp hj).2
      have hjs : j ∈ S := (Finset.mem_filter.mp hjt).1
      have haj : a ∈ A j := (Finset.mem_filter.mp hjt).2
      obtain ⟨b, hbA, hbB⟩ := Finset.not_disjoint_iff.mp (cross j hjs i his hji)
      have hab : a ≠ b := by intro h; exact han (h ▸ hbB)
      have heq : A j = {a,b} := pair_eq_of_mem (by rw [hA j hjs]) haj hbA hab
      exact Finset.mem_image.mpr ⟨b, hbB, heq.symm⟩
    have hinj : Set.InjOn A (↑(T.erase i) : Set ι) := by
      intro j hj k hk heq
      exact left_injective own cross
        ((Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).1)
        ((Finset.mem_filter.mp (Finset.mem_erase.mp hk).2).1) heq
    have hcard : (T.erase i).card ≤ 2 := calc
      (T.erase i).card = ((T.erase i).image A).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((B i).image (fun b => ({a,b} : Finset α))).card := Finset.card_le_card hsub
      _ ≤ (B i).card := Finset.card_image_le
      _ ≤ 2 := hB i his
    have he := Finset.card_erase_add_one hi
    omega
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    simp [he]

/-- The (2,2) set-pairs bound, by stars and two disjoint left pairs.
There is no restriction on the size of either ambient type. -/
theorem pair_system_card_le_six {S : Finset ι} {A B : ι → Finset α}
    (hA : ∀ i ∈ S, (A i).card = 2)
    (hB : ∀ i ∈ S, (B i).card ≤ 2)
    (own : ∀ i ∈ S, Disjoint (A i) (B i))
    (cross : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬Disjoint (A i) (B j)) : S.card ≤ 6 := by
  by_cases hd : ∃ i ∈ S, ∃ j ∈ S, Disjoint (A i) (A j)
  · obtain ⟨i, hi, j, hj, hd⟩ := hd
    let R := S \ {i,j}
    let U := ((A i).product (A j)).image (fun p => ({p.1,p.2} : Finset α))
    have hsub : R.image B ⊆ U := by
      intro s hs
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
      have hks : k ∈ S := (Finset.mem_sdiff.mp hk).1
      have hki : k ≠ i := by
        intro h; exact (Finset.mem_sdiff.mp hk).2 (by simp [h])
      have hkj : k ≠ j := by
        intro h; exact (Finset.mem_sdiff.mp hk).2 (by simp [h])
      obtain ⟨a, hai, hak⟩ := Finset.not_disjoint_iff.mp (cross i hi k hks hki.symm)
      obtain ⟨b, hbj, hbk⟩ := Finset.not_disjoint_iff.mp (cross j hj k hks hkj.symm)
      have hab : a ≠ b := by
        intro h
        exact Finset.disjoint_left.mp hd hai (h ▸ hbj)
      have heq := pair_eq_of_mem (hB k hks) hak hbk hab
      exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨hai,hbj⟩, heq.symm⟩
    have hinj : Set.InjOn B (↑R : Set ι) := by
      intro k hk l hl heq
      exact right_injective own cross (Finset.mem_sdiff.mp hk).1
        (Finset.mem_sdiff.mp hl).1 heq
    have hr : R.card ≤ 4 := calc
      R.card = (R.image B).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ U.card := Finset.card_le_card hsub
      _ ≤ ((A i).product (A j)).card := Finset.card_image_le
      _ = 4 := by rw [Finset.product_eq_sprod, Finset.card_product, hA i hi, hA j hj]
    have hp : (S ∩ {i,j}).card ≤ 2 := calc
      _ ≤ ({i,j} : Finset ι).card := Finset.card_le_card Finset.inter_subset_right
      _ ≤ 2 := by simpa using Finset.card_insert_le i ({j} : Finset ι)
    have he := Finset.card_sdiff_add_card_inter S ({i,j} : Finset ι)
    change R.card + (S ∩ {i,j}).card = S.card at he
    omega
  · by_cases hs : S.Nonempty
    · obtain ⟨i, hi⟩ := hs
      obtain ⟨a,b,hab,heq⟩ := Finset.card_eq_two.mp (hA i hi)
      have hsub : S ⊆ S.filter (fun k => a ∈ A k) ∪ S.filter (fun k => b ∈ A k) := by
        intro k hk
        have hnd : ¬Disjoint (A i) (A k) := by
          intro h; exact hd ⟨i,hi,k,hk,h⟩
        obtain ⟨x,hxi,hxk⟩ := Finset.not_disjoint_iff.mp hnd
        rw [heq] at hxi
        rcases Finset.mem_insert.mp hxi with h | h
        · apply Finset.mem_union_left
          exact Finset.mem_filter.mpr ⟨hk,h ▸ hxk⟩
        · apply Finset.mem_union_right
          exact Finset.mem_filter.mpr ⟨hk,(Finset.mem_singleton.mp h) ▸ hxk⟩
      calc
        S.card ≤ (S.filter (fun k => a ∈ A k) ∪ S.filter (fun k => b ∈ A k)).card :=
          Finset.card_le_card hsub
        _ ≤ (S.filter (fun k => a ∈ A k)).card + (S.filter (fun k => b ∈ A k)).card :=
          Finset.card_union_le _ _
        _ ≤ 3 + 3 := Nat.add_le_add (star_card_le_three hA hB own cross a)
          (star_card_le_three hA hB own cross b)
        _ = 6 := rfl
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-! ## Transversal-critical hypergraphs -/

/-- A finite simple hypergraph; edges are finite sets, so duplicates are absent. -/
abbrev Hypergraph (α : Type*) := Finset (Finset α)

/-- A transversal meets every edge. It need not be minimal. -/
def IsTransversal (H : Hypergraph α) (T : Finset α) : Prop :=
  ∀ e ∈ H, ¬Disjoint e T

/-- All edges have three distinct vertices. -/
def ThreeUniform (H : Hypergraph α) : Prop := ∀ e ∈ H, e.card = 3

/-- Transversal number exactly three, falling to at most two upon deletion
of any edge. The proof below also shows that the deletion number is exactly two. -/
def TransversalCriticalThree (H : Hypergraph α) : Prop :=
  (∃ T : Finset α, T.card = 3 ∧ IsTransversal H T) ∧
  (∀ T : Finset α, T.card ≤ 2 → ¬IsTransversal H T) ∧
  (∀ e ∈ H, ∃ T : Finset α, T.card ≤ 2 ∧ IsTransversal (H.erase e) T)

/-- The ordinary incidence degree, not an induced-subgraph or pair degree. -/
def degree (H : Hypergraph α) (v : α) : ℕ := (H.filter (fun e => v ∈ e)).card

/-- A small transversal after deleting `e` must avoid `e`. -/
lemma deletion_witness (H : Hypergraph α) (hc : TransversalCriticalThree H)
    (e : Finset α) (he : e ∈ H) :
    ∃ T : Finset α, T.card ≤ 2 ∧ Disjoint e T ∧ IsTransversal (H.erase e) T := by
  obtain ⟨T,hT,hhit⟩ := hc.2.2 e he
  refine ⟨T,hT,?_,hhit⟩
  by_contra hn
  apply hc.2.1 T hT
  intro f hf
  by_cases hfe : f = e
  · simpa only [hfe] using hn
  · exact hhit f (Finset.mem_erase.mpr ⟨hfe,hf⟩)

/-- The sharp pointwise bound: every vertex has degree at most six.
It holds over an arbitrary ambient type, without bounding the number of vertices. -/
theorem degree_le_six (H : Hypergraph α) (hu : ThreeUniform H)
    (hc : TransversalCriticalThree H) (v : α) : degree H v ≤ 6 := by
  classical
  let S := H.filter (fun e => v ∈ e)
  let A : Finset α → Finset α := fun e => e.erase v
  let B : Finset α → Finset α := fun e =>
    if he : e ∈ H then Classical.choose (deletion_witness H hc e he) else ∅
  have hspec (e : Finset α) (he : e ∈ H) :
      (B e).card ≤ 2 ∧ Disjoint e (B e) ∧ IsTransversal (H.erase e) (B e) := by
    simpa only [B, dif_pos he] using Classical.choose_spec (deletion_witness H hc e he)
  change S.card ≤ 6
  apply pair_system_card_le_six (A := A) (B := B)
  · intro e he
    have heH := (Finset.mem_filter.mp he).1
    have hev := (Finset.mem_filter.mp he).2
    have hh := Finset.card_erase_add_one hev
    have hu3 := hu e heH
    change (e.erase v).card = 2
    omega
  · intro e he
    exact (hspec e (Finset.mem_filter.mp he).1).1
  · intro e he
    exact Finset.disjoint_left.mpr (fun x hx =>
      Finset.disjoint_left.mp (hspec e (Finset.mem_filter.mp he).1).2.1
        (Finset.mem_erase.mp hx).2)
  · intro e he f hf hef
    have heH := (Finset.mem_filter.mp he).1
    have hfH := (Finset.mem_filter.mp hf).1
    have hvf := (Finset.mem_filter.mp hf).2
    have hehit := (hspec f hfH).2.2 e (Finset.mem_erase.mpr ⟨hef,heH⟩)
    obtain ⟨x,hxe,hxB⟩ := Finset.not_disjoint_iff.mp hehit
    have hxv : x ≠ v := by
      intro hx
      exact Finset.disjoint_left.mp (hspec f hfH).2.1 hvf (hx ▸ hxB)
    exact Finset.not_disjoint_iff.mpr ⟨x, Finset.mem_erase.mpr ⟨hxv,hxe⟩,hxB⟩

/-- Criticality cannot be vacuous: the hypergraph contains an edge. -/
lemma critical_nonempty (H : Hypergraph α) (hc : TransversalCriticalThree H) : H.Nonempty := by
  by_contra hn
  have he : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  apply hc.2.1 ∅ (by simp)
  intro e h
  simp [he] at h

/-- An active vertex realizes a degree between one and six. -/
theorem exists_positive_degree_le_six (H : Hypergraph α) (hu : ThreeUniform H)
    (hc : TransversalCriticalThree H) : ∃ v : α, 1 ≤ degree H v ∧ degree H v ≤ 6 := by
  obtain ⟨e,he⟩ := critical_nonempty H hc
  have hen : e.Nonempty := Finset.card_pos.mp (by rw [hu e he]; decide)
  obtain ⟨v,hv⟩ := hen
  refine ⟨v,?_,degree_le_six H hu hc v⟩
  exact Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hv⟩⟩

/-- The complete negative answer under the transversal interpretation. -/
theorem no_transversal_critical_minimum_degree_seven :
    ¬∃ H : Hypergraph α, ThreeUniform H ∧ TransversalCriticalThree H ∧
      ∀ v : α, 7 ≤ degree H v := by
  rintro ⟨H,hu,hc,hd⟩
  obtain ⟨v,_,hv⟩ := exists_positive_degree_le_six H hu hc
  have h7 := hd v
  omega

/-- Deleting an edge has transversal number exactly two, not merely at most two. -/
theorem deletion_transversal_exactly_two (H : Hypergraph α) (hu : ThreeUniform H)
    (hc : TransversalCriticalThree H) (e : Finset α) (he : e ∈ H) :
    (∃ T : Finset α, T.card = 2 ∧ IsTransversal (H.erase e) T) ∧
    (∀ T : Finset α, T.card < 2 → ¬IsTransversal (H.erase e) T) := by
  have hsmall : ∀ T : Finset α, T.card < 2 → ¬IsTransversal (H.erase e) T := by
    intro T hT hhit
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < e.card by rw [hu e he]; decide)
    have hcard : (insert v T).card ≤ 2 := (Finset.card_insert_le _ _).trans (by omega)
    apply hc.2.1 (insert v T) hcard
    intro f hf
    by_cases hfe : f = e
    · subst f
      exact Finset.not_disjoint_iff.mpr ⟨v,hv,Finset.mem_insert_self _ _⟩
    · obtain ⟨x,hxf,hxT⟩ := Finset.not_disjoint_iff.mp
        (hhit f (Finset.mem_erase.mpr ⟨hfe,hf⟩))
      exact Finset.not_disjoint_iff.mpr ⟨x,hxf,Finset.mem_insert_of_mem hxT⟩
  obtain ⟨T,hT,hhit⟩ := hc.2.2 e he
  refine ⟨⟨T,?_,hhit⟩,hsmall⟩
  have hn : ¬T.card < 2 := fun h => hsmall T h hhit
  omega

/-! ## Sharpness -/

def complete_five : Hypergraph (Fin 5) :=
  (Finset.univ : Finset (Fin 5)).powersetCard 3

/-- The bound is attained by the complete three-uniform hypergraph on five vertices. -/
theorem complete_five_properties :
    ThreeUniform complete_five ∧ TransversalCriticalThree complete_five ∧
      ∀ v : Fin 5, degree complete_five v = 6 := by
  constructor
  · unfold ThreeUniform complete_five
    decide
  constructor
  · unfold TransversalCriticalThree IsTransversal complete_five
    constructor
    · exact ⟨{0,1,2}, by decide, by decide⟩
    constructor
    · decide
    · decide
  · unfold degree complete_five
    decide

end JSP690Transversal
