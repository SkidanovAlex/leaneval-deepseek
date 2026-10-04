import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Metrizable.Uniformity
import Submission.Commons.Topology.ClosedGraph.exists_continuous_selection_of_closed_unique_fiber

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.Topology

open Set Function Filter
open scoped _root_.Topology

theorem homeo_level_times_of_flow_crossing {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {f : X → ℝ} (hf : Continuous f) {φ : X → ℝ → X}
    (hφ0 : ∀ x, φ x 0 = x) (hφc : Continuous fun p : X × ℝ => φ p.1 p.2)
    (hadd : ∀ x s t, φ (φ x s) t = φ x (s + t)) {a b : ℝ} (hab : a ≤ b) {N : ℝ}
    (hN : 0 ≤ N)
    (hcross : ∀ x, a ≤ f x → f x ≤ b → ∀ ℓ ∈ Set.Icc a b,
      ∃! t : ℝ, t ∈ Set.Icc (-N) N ∧ f (φ x t) = ℓ) :
    Nonempty (({x : X | a ≤ f x ∧ f x ≤ b}) ≃ₜ
      ({x : X | f x = a} ×ˢ Set.Icc (0 : ℝ) (b - a))) := by
  classical
  haveI hNc : CompactSpace ↥(Set.Icc (-N) N) := isCompact_iff_compactSpace.mp isCompact_Icc
  let S : Set X := {x | a ≤ f x ∧ f x ≤ b}
  let A : Set X := {x | f x = a}
  let I' : Set ℝ := Set.Icc (0 : ℝ) (b - a)
  -- ## Selection 1: from the slab to the level `{f = a}`, along the flow.
  have huniq1 : ∀ x : ↥S, ∃! y : ↥(Set.Icc (-N) N), f (φ x.1 y.1) = a := by
    intro x
    obtain ⟨t, ht, htu⟩ := hcross x.1 x.2.1 x.2.2 a ⟨le_refl a, hab⟩
    exact ⟨⟨t, ht.1⟩, ht.2, fun y hy => Subtype.ext (htu y.1 ⟨y.2, hy⟩)⟩
  have hclosed1 : IsClosed {p : ↥S × ↥(Set.Icc (-N) N) | f (φ p.1.1 p.2.1) = a} :=
    isClosed_eq (by fun_prop) continuous_const
  obtain ⟨sel1, hsel1c, hsel1m⟩ :=
    Commons.Topology.ClosedGraph.exists_continuous_selection_of_closed_unique_fiber
      {p : ↥S × ↥(Set.Icc (-N) N) | f (φ p.1.1 p.2.1) = a} hclosed1 huniq1
  -- ## Selection 2: from `{f = a} × [0, b-a]` back into the slab.
  have huniq2 : ∀ p : ↥A × ↥I', ∃! y : ↥(Set.Icc (-N) N), f (φ p.1.1 y.1) = a + p.2.1 := by
    intro p
    have hp1 : f p.1.1 = a := p.1.2
    obtain ⟨t, ht, htu⟩ := hcross p.1.1 (by rw [hp1]) (by rw [hp1]; exact hab) (a + p.2.1)
      ⟨by linarith [p.2.2.1], by linarith [p.2.2.2]⟩
    exact ⟨⟨t, ht.1⟩, ht.2, fun y hy => Subtype.ext (htu y.1 ⟨y.2, hy⟩)⟩
  have hclosed2 : IsClosed {q : (↥A × ↥I') × ↥(Set.Icc (-N) N) |
      f (φ q.1.1.1 q.2.1) = a + q.1.2.1} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  obtain ⟨sel2, hsel2c, hsel2m⟩ :=
    Commons.Topology.ClosedGraph.exists_continuous_selection_of_closed_unique_fiber
      {q : (↥A × ↥I') × ↥(Set.Icc (-N) N) | f (φ q.1.1.1 q.2.1) = a + q.1.2.1} hclosed2 huniq2
  -- ## Uniqueness helpers.
  have huniq1' : ∀ (x : ↥S) (y : ↥(Set.Icc (-N) N)), f (φ x.1 y.1) = a → y = sel1 x :=
    fun x y hy => (huniq1 x).unique hy (hsel1m x)
  have huniq2' : ∀ (p : ↥A × ↥I') (y : ↥(Set.Icc (-N) N)), f (φ p.1.1 y.1) = a + p.2.1 →
      y = sel2 p :=
    fun p y hy => (huniq2 p).unique hy (hsel2m p)
  -- ## The two maps.
  have hImem : ∀ x : ↥S, f x.1 - a ∈ I' :=
    fun x => ⟨sub_nonneg.mpr x.2.1, sub_le_sub_right x.2.2 a⟩
  have hGmem : ∀ p : ↥A × ↥I', φ p.1.1 (sel2 p).1 ∈ S :=
    fun p => ⟨by rw [hsel2m p]; linarith [p.2.2.1], by rw [hsel2m p]; linarith [p.2.2.2]⟩
  let F : ↥S → ↥A × ↥I' := fun x =>
    (⟨φ x.1 (sel1 x).1, hsel1m x⟩, ⟨f x.1 - a, hImem x⟩)
  let G : ↥A × ↥I' → ↥S := fun p => ⟨φ p.1.1 (sel2 p).1, hGmem p⟩
  have hFG : ∀ x : ↥S, G (F x) = x := by
    intro x
    have hmem : -(sel1 x).1 ∈ Set.Icc (-N) N :=
      ⟨by linarith [(sel1 x).2.2], by linarith [(sel1 x).2.1]⟩
    have hkey : (⟨-(sel1 x).1, hmem⟩ : ↥(Set.Icc (-N) N)) = sel2 (F x) := by
      apply huniq2'
      show f (φ (φ x.1 (sel1 x).1) (-(sel1 x).1)) = a + (f x.1 - a)
      rw [hadd x.1 (sel1 x).1 (-(sel1 x).1), add_neg_cancel, hφ0]
      ring
    apply Subtype.ext
    show φ (F x).1.1 (sel2 (F x)).1 = x.1
    have h4 : (sel2 (F x)).1 = -(sel1 x).1 := by
      have h5 := congrArg Subtype.val hkey
      simpa using h5.symm
    rw [h4, show (F x).1.1 = φ x.1 (sel1 x).1 from rfl]
    rw [hadd x.1 (sel1 x).1 (-(sel1 x).1), add_neg_cancel, hφ0]
  have hGF : ∀ p : ↥A × ↥I', F (G p) = p := by
    intro p
    have hmem : -(sel2 p).1 ∈ Set.Icc (-N) N :=
      ⟨by linarith [(sel2 p).2.2], by linarith [(sel2 p).2.1]⟩
    have hkey : (⟨-(sel2 p).1, hmem⟩ : ↥(Set.Icc (-N) N)) = sel1 (G p) := by
      apply huniq1'
      show f (φ (φ p.1.1 (sel2 p).1) (-(sel2 p).1)) = a
      rw [hadd p.1.1 (sel2 p).1 (-(sel2 p).1), add_neg_cancel, hφ0, show f p.1.1 = a from p.1.2]
    apply Prod.ext
    · apply Subtype.ext
      show φ (G p).1 (sel1 (G p)).1 = p.1.1
      have h4 : (sel1 (G p)).1 = -(sel2 p).1 := by
        have h5 := congrArg Subtype.val hkey
        simpa using h5.symm
      rw [h4, show (G p).1 = φ p.1.1 (sel2 p).1 from rfl]
      rw [hadd p.1.1 (sel2 p).1 (-(sel2 p).1), add_neg_cancel, hφ0]
    · apply Subtype.ext
      show f (G p).1 - a = p.2.1
      rw [show (G p).1 = φ p.1.1 (sel2 p).1 from rfl, hsel2m p]
      ring
  have hFc : Continuous F :=
    Continuous.prodMk
      (Continuous.subtype_mk
        (hφc.comp (Continuous.prodMk continuous_subtype_val (continuous_subtype_val.comp hsel1c)))
        hsel1m)
      (Continuous.subtype_mk ((hf.comp continuous_subtype_val).sub continuous_const) hImem)
  have hGc : Continuous G :=
    Continuous.subtype_mk (hφc.comp (Continuous.prodMk
      (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp hsel2c))) hGmem
  refine ⟨?_⟩
  let e : ↥S ≃ₜ ↥A × ↥I' :=
    { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF,
      continuous_toFun := hFc, continuous_invFun := hGc }
  exact e.trans (Homeomorph.Set.prod A I').symm

end Commons.Topology