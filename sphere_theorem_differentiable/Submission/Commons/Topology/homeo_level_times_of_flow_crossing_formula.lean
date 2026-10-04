import Mathlib.Topology.Algebra.Ring.Real
import Submission.Commons.Topology.ClosedGraph.exists_continuous_selection_of_closed_unique_fiber

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.Topology

open Set

theorem homeo_level_times_of_flow_crossing_formula {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {f : X → ℝ} (hf : Continuous f) {φ : X → ℝ → X}
    (hφ0 : ∀ x, φ x 0 = x) (hφc : Continuous fun p : X × ℝ => φ p.1 p.2)
    (hadd : ∀ x s t, φ (φ x s) t = φ x (s + t)) {a b : ℝ} (hab : a ≤ b) {N : ℝ}
    (hN : 0 ≤ N)
    (hcross : ∀ x, a ≤ f x → f x ≤ b → ∀ ℓ ∈ Set.Icc a b,
      ∃! t : ℝ, t ∈ Set.Icc (-N) N ∧ f (φ x t) = ℓ) :
    ∃ Φ : ({x : X | f x = a} ×ˢ Set.Icc (0 : ℝ) (b - a)) ≃ₜ
        {x : X | a ≤ f x ∧ f x ≤ b},
      ∀ p, f ((Φ p : X)) = a + (p.1.2 : ℝ) := by
  classical
  haveI hNc : CompactSpace ↥(Set.Icc (-N) N) := isCompact_iff_compactSpace.mp isCompact_Icc
  let S : Set X := {x | a ≤ f x ∧ f x ≤ b}
  let A : Set X := {x | f x = a}
  let I' : Set ℝ := Set.Icc (0 : ℝ) (b - a)
  have hAclosed : IsClosed A := by
    have h : A = f ⁻¹' ({a} : Set ℝ) := rfl
    rw [h]; exact isClosed_singleton.preimage hf
  haveI hAc : CompactSpace ↥A := isCompact_iff_compactSpace.mp hAclosed.isCompact
  haveI hI'c : CompactSpace ↥I' := isCompact_iff_compactSpace.mp isCompact_Icc
  -- ## The crossing-time selection on `{f = a} × [0, b-a]`.
  have huniq2 : ∀ p : ↥A × ↥I', ∃! y : ↥(Set.Icc (-N) N),
      f (φ p.1.1 y.1) = a + p.2.1 := by
    intro p
    have hp1 : f p.1.1 = a := p.1.2
    obtain ⟨t, ht, htu⟩ := hcross p.1.1 (by rw [hp1])
      (by rw [hp1]; exact hab) (a + p.2.1)
      ⟨by linarith [p.2.2.1], by linarith [p.2.2.2]⟩
    exact ⟨⟨t, ht.1⟩, ht.2, fun y hy => Subtype.ext (htu y.1 ⟨y.2, hy⟩)⟩
  have hclosed2 : IsClosed {q : (↥A × ↥I') × ↥(Set.Icc (-N) N) |
      f (φ q.1.1.1 q.2.1) = a + q.1.2.1} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  obtain ⟨sel2, hsel2c, hsel2m⟩ :=
    ClosedGraph.exists_continuous_selection_of_closed_unique_fiber
      {q : (↥A × ↥I') × ↥(Set.Icc (-N) N) |
        f (φ q.1.1.1 q.2.1) = a + q.1.2.1} hclosed2 huniq2
  have huniq2' : ∀ (p : ↥A × ↥I') (y : ↥(Set.Icc (-N) N)),
      f (φ p.1.1 y.1) = a + p.2.1 → y = sel2 p :=
    fun p y hy => (huniq2 p).unique hy (hsel2m p)
  -- ## The homeomorphism `G : {f = a} × [0, b-a] → {a ≤ f ≤ b}` and its inverse.
  have hGmem : ∀ p : ↥A × ↥I', φ p.1.1 (sel2 p).1 ∈ S :=
    fun p => ⟨by rw [hsel2m p]; linarith [p.2.2.1],
              by rw [hsel2m p]; linarith [p.2.2.2]⟩
  let G : ↥A × ↥I' → ↥S := fun p => ⟨φ p.1.1 (sel2 p).1, hGmem p⟩
  have hGcont : Continuous G :=
    Continuous.subtype_mk (hφc.comp (Continuous.prodMk
      (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp hsel2c))) hGmem
  have hGinj : Function.Injective G := by
    intro p p' hp
    have hz : (G p : X) = (G p' : X) := congrArg Subtype.val hp
    have hs : p.2 = p'.2 := by
      apply Subtype.ext
      have h1 : f ((G p : ↥S) : X) = a + p.2.1 := hsel2m p
      have h2 : f ((G p' : ↥S) : X) = a + p'.2.1 := hsel2m p'
      have h3 : a + p.2.1 = a + p'.2.1 := by rw [← h1, ← h2, hz]
      linarith
    have hfst : p.1 = p'.1 := by
      apply Subtype.ext
      have hkey := hcross (G p : X) (G p).2.1 (G p).2.2 a ⟨le_refl a, hab⟩
      have e1 : -(sel2 p).1 ∈ Set.Icc (-N) N ∧
          f (φ (G p : X) (-(sel2 p).1)) = a := by
        refine ⟨⟨by linarith [(sel2 p).2.2], by linarith [(sel2 p).2.1]⟩, ?_⟩
        rw [show (G p : X) = φ p.1.1 (sel2 p).1 from rfl,
          hadd p.1.1 (sel2 p).1 (-(sel2 p).1), add_neg_cancel, hφ0]
        exact p.1.2
      have e2 : -(sel2 p').1 ∈ Set.Icc (-N) N ∧
          f (φ (G p : X) (-(sel2 p').1)) = a := by
        refine ⟨⟨by linarith [(sel2 p').2.2], by linarith [(sel2 p').2.1]⟩, ?_⟩
        rw [hz, show (G p' : X) = φ p'.1.1 (sel2 p').1 from rfl,
          hadd p'.1.1 (sel2 p').1 (-(sel2 p').1), add_neg_cancel, hφ0]
        exact p'.1.2
      have hτ : -(sel2 p).1 = -(sel2 p').1 := hkey.unique e1 e2
      have hy1 : p.1.1 = φ (G p : X) (-(sel2 p).1) := by
        rw [show (G p : X) = φ p.1.1 (sel2 p).1 from rfl,
          hadd p.1.1 (sel2 p).1 (-(sel2 p).1), add_neg_cancel, hφ0]
      have hy2 : p'.1.1 = φ (G p' : X) (-(sel2 p').1) := by
        rw [show (G p' : X) = φ p'.1.1 (sel2 p').1 from rfl,
          hadd p'.1.1 (sel2 p').1 (-(sel2 p').1), add_neg_cancel, hφ0]
      rw [hy1, hy2, hz, hτ]
    exact Prod.ext hfst hs
  have hGsurj : Function.Surjective G := by
    intro x
    obtain ⟨t, ht, _⟩ := hcross x.1 x.2.1 x.2.2 a ⟨le_refl a, hab⟩
    let y : ↥A := ⟨φ x.1 t, by show f (φ x.1 t) = a; exact ht.2⟩
    let s : ↥I' := ⟨f x.1 - a, ⟨sub_nonneg.mpr x.2.1, sub_le_sub_right x.2.2 a⟩⟩
    refine ⟨(y, s), ?_⟩
    have hmem : -t ∈ Set.Icc (-N) N := ⟨by linarith [ht.1.2], by linarith [ht.1.1]⟩
    have hsel : sel2 (y, s) = ⟨-t, hmem⟩ := by
      apply Eq.symm
      apply huniq2'
      show f (φ y.1 (-t)) = a + s.1
      rw [show y.1 = φ x.1 t from rfl, hadd x.1 t (-t), add_neg_cancel, hφ0]
      show f x.1 = a + (f x.1 - a)
      ring
    apply Subtype.ext
    show (G (y, s) : X) = x.1
    rw [show (G (y, s) : X) = φ y.1 (sel2 (y, s)).1 from rfl,
      show (sel2 (y, s)).1 = -t from congrArg Subtype.val hsel,
      show y.1 = φ x.1 t from rfl, hadd x.1 t (-t), add_neg_cancel, hφ0]
  -- ## Assemble.
  let e : (↥A × ↥I') ≃ ↥S := Equiv.ofBijective G ⟨hGinj, hGsurj⟩
  have hec : Continuous e := hGcont
  let hh : (↥A × ↥I') ≃ₜ ↥S := Continuous.homeoOfEquivCompactToT2 hec
  have key : ∀ q : ↥A × ↥I', f ((hh q : ↥S) : X) = a + q.2.1 := fun q => hsel2m q
  refine ⟨(Homeomorph.Set.prod A I').trans hh, ?_⟩
  intro p
  rw [Homeomorph.trans_apply, key]
  have hq : ((Homeomorph.Set.prod A I') p).2.1 = p.1.2 := rfl
  rw [hq]

end Commons.Topology
