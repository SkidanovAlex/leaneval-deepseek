import Mathlib
import Submission.Commons.Topology.OneManifold.arc_extension_or_compact
import Submission.Commons.Topology.OneManifold.nested_open_arcs_union_is_open_arc
import Submission.Commons.Topology.Homeomorph.open_interval_affine

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

/-!
# Classification dichotomy of connected one-dimensional manifolds

A connected Hausdorff second-countable topological space in which every
point has an open neighbourhood homeomorphic to an open real interval (a
connected topological 1-manifold without boundary) is homeomorphic either
to the open unit interval `(0,1)` or is compact.

This is the Layer-3 assembly of the team's one-dimensional end theory:

* **Layer 1** (`arc_extension_or_compact`, in the commons): every PROPER
  open arc of such a space extends to a strictly larger open arc, unless
  the whole space is compact.
* **Layer 2** (`nested_open_arcs_union_is_open_arc`, in the commons): the
  union of a nested countable family of open arcs is again an open arc.
* **Layer 3** (this file): Zorn maximal-arc assembly.  Given a base open
  arc `U₀`, consider the family `OpenArc U₀` of proper open arcs
  containing `U₀`.  Second countability makes every chain of this family
  countably cofinal (`eq_open_union_nat`), the cofinal sequence is
  re-ordered into a nested one (`nested_cofinal`), and Layer 2 shows the
  union is again a proper open arc unless it fills `X` — which would make
  `X` itself chartable.  Zorn yields a maximal member `m`; if `m ≠ univ`,
  Layer 1 extends it (contradiction) or forces `X` compact.
-/


/-- An open unit-arc chart in a locally interval-charted space exists near
every point. -/
lemma local_unit_arc {X : Type*} [TopologicalSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    (x : X) : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Nonempty (ORI ≃ₜ U) := by
  rcases hLoc x with ⟨U, hUopen, hxU, lo, hi, e⟩
  rcases e with ⟨e'⟩
  have hlt : lo < hi := by
    rcases e'.surjective ⟨x, hxU⟩ with ⟨t, _⟩
    exact lt_trans t.2.1 t.2.2
  rcases Commons.Topology.Homeomorph.open_interval_affine (a := lo) (b := hi) (c := 0) (d := 1)
      hlt (by norm_num) with ⟨φ⟩
  exact ⟨U, hUopen, hxU, ⟨φ.symm.trans e'⟩⟩

/-- The family of proper open arcs containing the base arc `U₀`. -/
def OpenArc {X : Type*} [TopologicalSpace X] (U₀ : Set X) : Set (Set X) :=
  {P : Set X | IsOpen P ∧ U₀ ⊆ P ∧ P ≠ Set.univ ∧ Nonempty (ORI ≃ₜ P)}

/-- In a chain of open sets (totally ordered by inclusion), the countable
subfamily produced by second countability can be re-ordered to a nested
one which still dominates every member of the subfamily. -/
lemma nested_cofinal {X : Type*} {c : Set (Set X)} (w : ℕ → Set X)
    (hw : ∀ n, w n ∈ c)
    (hcmp : ∀ a b : Set X, a ∈ c → b ∈ c → a ⊆ b ∨ b ⊆ a) :
    ∃ v : ℕ → Set X,
      (∀ n, v n ∈ c) ∧ (∀ n, w n ⊆ v n) ∧ (∀ n, v n ⊆ v (n + 1)) := by
  classical
  let P : ℕ → Set X → Prop := fun n u => u ∈ c ∧ w n ⊆ u
  have hstep : ∀ (n : ℕ) (acc : Set X), P n acc → ∃ u : Set X, P (n + 1) u ∧ acc ⊆ u := by
    intro n acc hp
    rcases hp with ⟨hacc_c, hacc_w⟩
    have ht : acc ⊆ w (n + 1) ∨ w (n + 1) ⊆ acc := hcmp acc (w (n + 1)) hacc_c (hw (n + 1))
    rcases ht with h | h
    · refine ⟨w (n + 1), ?_, h⟩
      exact ⟨hw (n + 1), Subset.rfl⟩
    · refine ⟨acc, ?_, Subset.rfl⟩
      exact ⟨hacc_c, h⟩
  let v' : ∀ n : ℕ, {u : Set X // P n u} :=
    Nat.rec (motive := fun n : ℕ => {u : Set X // P n u})
      ⟨w 0, hw 0, Subset.rfl⟩
      (fun n acc =>
        let u : Set X := Classical.choose (hstep n (acc : Set X) acc.2)
        ⟨u, (Classical.choose_spec (hstep n (acc : Set X) acc.2)).1⟩)
  let v : ℕ → Set X := fun n => (v' n).1
  refine ⟨v, ?_, ?_, ?_⟩
  · intro n
    exact (v' n).2.1
  · intro n
    exact (v' n).2.2
  · intro n
    have hs := Classical.choose_spec (hstep n (v' n).1 (v' n).2)
    exact hs.2

/-- Every chain of `OpenArc U₀` has an upper bound in `OpenArc U₀` — unless
the chain fills the whole space, which would make `X` itself an open arc
(contradicting `hArc`).  Second countability makes the chain countably
cofinal; `nested_cofinal` re-orders the cofinal family to be nested; and
Layer 2 (`nested_open_arcs_union_is_open_arc`) shows the union is an open
arc. -/
lemma open_arcs_chain_upper_bound {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X]
    (hArc : ¬ Nonempty (ORI ≃ₜ X))
    {U₀ : Set X} (hU₀mem : U₀ ∈ OpenArc U₀)
    {c : Set (Set X)} (hc : c ⊆ OpenArc U₀)
    (hchain : IsChain (fun A B : Set X => A ⊆ B) c) :
    ∃ ub ∈ OpenArc U₀, ∀ s ∈ c, s ⊆ ub := by
  classical
  by_cases hcempty : c = ∅
  · refine ⟨U₀, hU₀mem, ?_⟩
    intro s hs
    exact (by simpa [hcempty] using hs)
  · have hcne : c.Nonempty := Set.nonempty_iff_ne_empty.mpr hcempty
    haveI : Nonempty {s : Set X // s ∈ c} := ⟨Classical.choose hcne, Classical.choose_spec hcne⟩
    let U : {s : Set X // s ∈ c} → Set X := fun s => (s : Set X)
    have hUopen : ∀ s : {s : Set X // s ∈ c}, IsOpen (U s) := by
      intro s
      exact (hc s.2).1
    rcases eq_open_union_nat (X := X) (U := U) hUopen with ⟨k, hk⟩
    let w : ℕ → Set X := fun n => U (k n)
    have hw_mem : ∀ n : ℕ, w n ∈ c := by
      intro n
      exact (k n).2
    have hw_cover : ∀ s : Set X, s ∈ c → s ⊆ ⋃ n, w n := by
      intro s hs x hx
      have hxU : x ∈ ⋃ i : {s : Set X // s ∈ c}, U i := by
        exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩
      have hxw0 : x ∈ ⋃ n, U (k n) := by
        rw [← hk] at hxU
        exact hxU
      rcases Set.mem_iUnion.mp hxw0 with ⟨n, hxn⟩
      exact Set.mem_iUnion.mpr ⟨n, by simpa [w] using hxn⟩
    have hcmp : ∀ a b : Set X, a ∈ c → b ∈ c → a ⊆ b ∨ b ⊆ a := by
      intro a b ha hb
      by_cases hab : a = b
      · subst b
        exact Or.inl Subset.rfl
      · exact hchain ha hb hab
    rcases nested_cofinal (c := c) w hw_mem hcmp with ⟨v, hv_mem, hw_le_v, hv_nest⟩
    have hv_open : ∀ n : ℕ, IsOpen (v n) := by
      intro n
      exact (hc (hv_mem n)).1
    have hv_chart : ∀ n : ℕ, Nonempty (ORI ≃ₜ v n) := by
      intro n
      exact (hc (hv_mem n)).2.2.2
    rcases nested_open_arcs_union_is_open_arc (X := X) v hv_open hv_nest hv_chart with ⟨eub⟩
    have hub_open : IsOpen (⋃ n, v n) := isOpen_iUnion hv_open
    have hU₀le : U₀ ⊆ ⋃ n, v n := by
      intro x hx
      have hxw : x ∈ w 0 := (hc (hw_mem 0)).2.1 hx
      have hx0 : x ∈ v 0 := hw_le_v 0 hxw
      exact Set.mem_iUnion.mpr ⟨0, hx0⟩
    by_cases hub_univ : (⋃ n, v n) = Set.univ
    · exfalso
      apply hArc
      rw [hub_univ] at eub
      exact ⟨eub.trans (Homeomorph.Set.univ X)⟩
    · refine ⟨⋃ n, v n, ⟨hub_open, hU₀le, hub_univ, ⟨eub⟩⟩, ?_⟩
      intro s hs
      exact fun x hx => by
        have hxw : x ∈ ⋃ n, w n := hw_cover s hs hx
        rcases Set.mem_iUnion.mp hxw with ⟨n, hxn⟩
        exact Set.mem_iUnion.mpr ⟨n, hw_le_v n hxn⟩

/-- **Layer 3 — the interval/circle dichotomy.**  A connected Hausdorff
second-countable locally interval-charted space is homeomorphic to the
open unit interval `(0,1)` or is compact.  (Maximal-arc exhaustion using
Zorn; Layers 1 and 2 come from the commons.) -/
theorem oneManifold_dichotomy {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [Nonempty X] [ConnectedSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U)) :
    Nonempty ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} ≃ₜ X) ∨ CompactSpace X := by
  classical
  by_cases hArc : Nonempty (ORI ≃ₜ X)
  · exact Or.inl hArc
  · right
    let x₀ : X := Classical.choice (inferInstance : Nonempty X)
    rcases local_unit_arc (X := X) hLoc x₀ with ⟨U₀, hU₀open, hx₀U₀, eU₀⟩
    have hU₀ne : U₀ ≠ Set.univ := by
      intro hU
      apply hArc
      rcases eU₀ with ⟨e⟩
      rw [hU] at e
      exact ⟨e.trans (Homeomorph.Set.univ X)⟩
    have hU₀S : U₀ ∈ OpenArc U₀ := ⟨hU₀open, Subset.rfl, hU₀ne, eU₀⟩
    have hbdd : ∀ c : Set (Set X), c ⊆ OpenArc U₀ →
        IsChain (fun A B : Set X => A ⊆ B) c → ∃ ub ∈ OpenArc U₀, ∀ s ∈ c, s ⊆ ub := by
      intro c hcS hch
      exact open_arcs_chain_upper_bound hArc hU₀S hcS hch
    rcases zorn_subset (OpenArc U₀) hbdd with ⟨m, hm⟩
    have hmS : m ∈ OpenArc U₀ := hm.1
    have hmmax : ∀ y : Set X, y ∈ OpenArc U₀ → m ⊆ y → y ⊆ m := by
      intro y hy
      exact hm.2 hy
    have hmopen : IsOpen m := hmS.1
    have hU₀m : U₀ ⊆ m := hmS.2.1
    have hmne : m ≠ Set.univ := hmS.2.2.1
    have hem : Nonempty (ORI ≃ₜ m) := hmS.2.2.2
    rcases arc_extension_or_compact hLoc hmopen hem hmne with hExt | hC
    · exfalso
      rcases hExt with ⟨Q, hQopen, hPQ, hQarc⟩
      by_cases hQuniv : Q = Set.univ
      · apply hArc
        rcases hQarc with ⟨eq⟩
        rw [hQuniv] at eq
        exact ⟨eq.trans (Homeomorph.Set.univ X)⟩
      · have hQS : Q ∈ OpenArc U₀ := ⟨hQopen, Subset.trans hU₀m hPQ.1, hQuniv, hQarc⟩
        have hQm : Q ⊆ m := hmmax Q hQS hPQ.1
        exact hPQ.2 hQm
    · exact hC

end Commons.Topology.OneManifold
