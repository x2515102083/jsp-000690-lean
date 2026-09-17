import Std

/-!
# JSP-000690: Li's chromatic-critical hypergraph

Mathematical construction: Ruiliang Li, arXiv:2512.24850v1,
Theorems 1.2 and 4.1, equation (5). This is the CHROMATIC interpretation.
The transversal-number interpretation is a different theorem.

Formalization prepared for GitHub account x2515102083 with OpenAI Codex.
See ATTRIBUTION.md for prior formalizations consulted and the scope of credit.
SPDX-License-Identifier: MIT
-/

namespace JSP690

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

abbrev Edge (n : Nat) := Fin n × Fin n × Fin n
abbrev Hypergraph (n : Nat) := List (Edge n)

/-- An edge is represented by its three vertices in increasing order.
Together with `Nodup`, this is a simple (not multi-) 3-uniform hypergraph. -/
def SimpleThreeUniform {n : Nat} (G : Hypergraph n) : Prop :=
  G.Nodup ∧ ∀ e ∈ G, e.1 < e.2.1 ∧ e.2.1 < e.2.2

/-- Weak coloring: no edge has all its vertices the same color. -/
def Proper {n : Nat} {α : Type} (G : Hypergraph n) (c : Fin n → α) : Prop :=
  ∀ e ∈ G, ¬ (c e.1 = c e.2.1 ∧ c e.2.1 = c e.2.2)

instance {n : Nat} {α : Type} [DecidableEq α]
    (G : Hypergraph n) (c : Fin n → α) : Decidable (Proper G c) :=
  inferInstanceAs (Decidable
    (∀ e ∈ G, ¬ (c e.1 = c e.2.1 ∧ c e.2.1 = c e.2.2)))

def Colorable {n : Nat} (G : Hypergraph n) (k : Nat) : Prop :=
  ∃ c : Fin n → Fin k, Proper G c

def ChromaticNumberExactly {n : Nat} (G : Hypergraph n) (k : Nat) : Prop :=
  Colorable G k ∧ ∀ m, m < k → ¬ Colorable G m

def incident {n : Nat} (v : Fin n) (e : Edge n) : Bool :=
  v == e.1 || v == e.2.1 || v == e.2.2

def degree {n : Nat} (G : Hypergraph n) (v : Fin n) : Nat :=
  (G.filter (incident v)).length

def eraseEdge {n : Nat} (G : Hypergraph n) (e : Edge n) : Hypergraph n :=
  G.filter (fun f => f != e)

def eraseVertex {n : Nat} (G : Hypergraph n) (v : Fin n) : Hypergraph n :=
  G.filter (fun e => !incident v e)

/-- Colors on deleted vertices are irrelevant; these total functions restrict
to proper colorings on the remaining vertices. -/
def ChromaticCriticalThree {n : Nat} (G : Hypergraph n) : Prop :=
  ChromaticNumberExactly G 3 ∧
  (∀ e ∈ G, Colorable (eraseEdge G e) 2) ∧
  (∀ v : Fin n, Colorable (eraseVertex G v) 2)

theorem proper_recolor {n : Nat} {α β : Type} {G : Hypergraph n}
    {c : Fin n → α} (hc : Proper G c) (f : α → β)
    (hinj : ∀ a b, f a = f b → a = b) : Proper G (fun v => f (c v)) := by
  intro e he hmono
  exact hc e he ⟨hinj _ _ hmono.1, hinj _ _ hmono.2⟩

theorem colorable_mono {n k l : Nat} {G : Hypergraph n}
    (hkl : k ≤ l) (h : Colorable G k) : Colorable G l := by
  obtain ⟨c, hc⟩ := h
  let f : Fin k → Fin l := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hkl⟩
  refine ⟨fun v => f (c v), proper_recolor hc f ?_⟩
  intro a b hab
  have hv : (f a).val = (f b).val := congrArg (fun i : Fin l => i.val) hab
  exact Fin.ext hv

/-- Exhaustive binary colorings for *any* finite vertex count. -/
def binaryColorings : (n : Nat) → List (Fin n → Bool)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 => (binaryColorings n).flatMap fun c =>
      [Fin.cases false c, Fin.cases true c]

/-- The enumeration covers arbitrary functions, not just a sample of masks. -/
theorem binaryColorings_complete (n : Nat) (c : Fin n → Bool) :
    c ∈ binaryColorings n := by
  induction n with
  | zero =>
      have h : c = (fun i => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      simp [binaryColorings, h]
  | succ n ih =>
      have ht := ih (fun i => c i.succ)
      have hc : c = Fin.cases (c 0) (fun i => c i.succ) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      have hm : Fin.cases (c 0) (fun i => c i.succ) ∈ binaryColorings (n + 1) := by
        apply List.mem_flatMap.mpr
        refine ⟨(fun i => c i.succ), ht, ?_⟩
        cases c 0 <;> simp
      rw [hc]
      exact hm

/-- Equation (5), with the paper's vertices 1..9 shifted to 0..8. -/
def liGraph : Hypergraph 9 :=
  [(0,1,2), (0,1,8), (0,2,7), (0,3,5), (0,3,7), (0,3,8),
   (0,4,6), (0,4,7), (0,4,8), (0,5,6),
   (1,2,5), (1,2,6), (1,3,8), (1,4,8), (1,5,6),
   (2,3,7), (2,4,7), (2,5,6), (3,5,7), (3,5,8), (4,6,7), (4,6,8)]

theorem liGraph_simple : SimpleThreeUniform liGraph := by
  unfold SimpleThreeUniform
  decide

theorem liGraph_edge_count : liGraph.length = 22 := by decide

theorem liGraph_degrees :
    ∀ v : Fin 9, degree liGraph v = if v = 0 then 10 else 7 := by decide

theorem liGraph_minimum_degree :
    (∀ v : Fin 9, 7 ≤ degree liGraph v) ∧ degree liGraph 1 = 7 := by decide

theorem binary_obstruction :
    ∀ c ∈ binaryColorings 9, ¬ Proper liGraph c := by decide

theorem no_binary_coloring (c : Fin 9 → Bool) : ¬ Proper liGraph c :=
  binary_obstruction c (binaryColorings_complete 9 c)

def finTwoToBool (i : Fin 2) : Bool := i.val == 1

theorem finTwoToBool_injective :
    ∀ a b : Fin 2, finTwoToBool a = finTwoToBool b → a = b := by decide

theorem liGraph_not_two_colorable : ¬ Colorable liGraph 2 := by
  intro h
  obtain ⟨c, hc⟩ := h
  exact no_binary_coloring (fun v => finTwoToBool (c v))
    (proper_recolor hc finTwoToBool finTwoToBool_injective)

/-- The explicit 3-coloring of Li's Lemma 4.4. -/
def threeColor (v : Fin 9) : Fin 3 :=
  if v.val = 0 ∨ v.val = 1 ∨ v.val = 3 ∨ v.val = 4 then 0
  else if v.val = 6 then 2 else 1

theorem liGraph_three_colorable : Proper liGraph threeColor := by decide

theorem liGraph_chromatic_number : ChromaticNumberExactly liGraph 3 := by
  refine ⟨⟨threeColor, liGraph_three_colorable⟩, ?_⟩
  intro m hm hcolor
  exact liGraph_not_two_colorable (colorable_mono (by omega) hcolor)

/-- A mask is used only to supply a concrete coloring witness, never as an
unproved replacement for quantification over arbitrary coloring functions. -/
def maskColor (mask : Nat) (v : Fin 9) : Fin 2 :=
  if mask.testBit v.val then 1 else 0

/-- Small witness pool generated by the auxiliary exhaustive cross-check.
Lean checks the witnesses itself; the generator is not in the trusted base. -/
def witnessMasks : List Nat :=
  [27,29,30,31,51,53,58,59,60,62,75,77,91,94,163,178,179,186,195,202,203,218]

theorem edge_deletion_certificates :
    ∀ e ∈ liGraph, ∃ m ∈ witnessMasks, Proper (eraseEdge liGraph e) (maskColor m) := by
  decide

theorem vertex_deletion_certificates :
    ∀ v : Fin 9, ∃ m ∈ witnessMasks, Proper (eraseVertex liGraph v) (maskColor m) := by
  decide

theorem liGraph_edge_critical : ∀ e ∈ liGraph, Colorable (eraseEdge liGraph e) 2 := by
  intro e he
  obtain ⟨m, _, hm⟩ := edge_deletion_certificates e he
  exact ⟨maskColor m, hm⟩

theorem liGraph_vertex_critical : ∀ v : Fin 9, Colorable (eraseVertex liGraph v) 2 := by
  intro v
  obtain ⟨m, _, hm⟩ := vertex_deletion_certificates v
  exact ⟨maskColor m, hm⟩

theorem liGraph_critical : ChromaticCriticalThree liGraph :=
  ⟨liGraph_chromatic_number, liGraph_edge_critical, liGraph_vertex_critical⟩

/-- A semantic formulation covering arbitrary proper subhypergraphs, including
simultaneous deletion of vertices and edges. `W` is the surviving vertex set.
The returned total coloring restricts to `W`. -/
def AllProperSubgraphsTwoColorable {n : Nat} (G : Hypergraph n) : Prop :=
  ∀ (W : Fin n → Prop) (F : Hypergraph n),
    (∀ e ∈ F, e ∈ G) →
    (∀ e ∈ F, W e.1 ∧ W e.2.1 ∧ W e.2.2) →
    ((∃ v, ¬ W v) ∨ (∃ e ∈ G, e ∉ F)) → Colorable F 2

theorem liGraph_all_proper_subgraphs : AllProperSubgraphsTwoColorable liGraph := by
  intro W F hsub hverts hproper
  rcases hproper with ⟨v, hv⟩ | ⟨e, he, hmissing⟩
  · obtain ⟨c, hc⟩ := liGraph_vertex_critical v
    refine ⟨c, ?_⟩
    intro f hf
    apply hc f
    apply List.mem_filter.mpr
    refine ⟨hsub f hf, ?_⟩
    have ha : v ≠ f.1 := by
      intro h
      exact hv (h ▸ (hverts f hf).1)
    have hb : v ≠ f.2.1 := by
      intro h
      exact hv (h ▸ (hverts f hf).2.1)
    have hd : v ≠ f.2.2 := by
      intro h
      exact hv (h ▸ (hverts f hf).2.2)
    simp [incident, ha, hb, hd]
  · obtain ⟨c, hc⟩ := liGraph_edge_critical e he
    refine ⟨c, ?_⟩
    intro f hf
    apply hc f
    apply List.mem_filter.mpr
    refine ⟨hsub f hf, ?_⟩
    have hne : f ≠ e := by
      intro h
      exact hmissing (h ▸ hf)
    simp [hne]

theorem nonempty_not_one_colorable {n : Nat} {G : Hypergraph n}
    (hne : ∃ e, e ∈ G) : ¬ Colorable G 1 := by
  obtain ⟨e, he⟩ := hne
  rintro ⟨c, hc⟩
  have singleton : ∀ a b : Fin 1, a = b := by decide
  exact hc e he ⟨singleton _ _, singleton _ _⟩

theorem edge_deletion_nonempty : ∀ e ∈ liGraph, ∃ f ∈ liGraph,
    f ∈ eraseEdge liGraph e := by decide

theorem vertex_deletion_nonempty : ∀ v : Fin 9, ∃ f ∈ liGraph,
    f ∈ eraseVertex liGraph v := by decide

theorem liGraph_deleted_edge_chromatic_two :
    ∀ e ∈ liGraph, ChromaticNumberExactly (eraseEdge liGraph e) 2 := by
  intro e he
  refine ⟨liGraph_edge_critical e he, ?_⟩
  intro m hm hcolor
  obtain ⟨f, _, hf⟩ := edge_deletion_nonempty e he
  exact nonempty_not_one_colorable ⟨f, hf⟩ (colorable_mono (by omega) hcolor)

theorem liGraph_deleted_vertex_chromatic_two :
    ∀ v : Fin 9, ChromaticNumberExactly (eraseVertex liGraph v) 2 := by
  intro v
  refine ⟨liGraph_vertex_critical v, ?_⟩
  intro m hm hcolor
  obtain ⟨f, _, hf⟩ := vertex_deletion_nonempty v
  exact nonempty_not_one_colorable ⟨f, hf⟩ (colorable_mono (by omega) hcolor)

/-- Complete existential statement of the catalog's chromatic problem.
There is no mathematical hypothesis other than the definitions above. -/
theorem jsp000690 :
    ∃ n : Nat, ∃ G : Hypergraph n,
      SimpleThreeUniform G ∧ ChromaticCriticalThree G ∧
      AllProperSubgraphsTwoColorable G ∧
      (∀ v : Fin n, 7 ≤ degree G v) ∧ (∃ v : Fin n, degree G v = 7) := by
  exact ⟨9, liGraph, liGraph_simple, liGraph_critical,
    liGraph_all_proper_subgraphs, liGraph_minimum_degree.1,
    ⟨1, liGraph_minimum_degree.2⟩⟩

end JSP690
