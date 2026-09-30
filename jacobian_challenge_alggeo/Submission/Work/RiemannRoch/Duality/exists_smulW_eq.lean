import Mathlib
import Submission.Work.RiemannRoch.Duality.Basic
import Submission.Work.RiemannRoch.Duality.finrank_WD
import Submission.Work.RiemannRoch.Duality.sum_l_le_finrank_WD
import Submission.Work.RiemannRoch.Duality.deg_le_of_mem_WD
import Submission.Work.RiemannRoch.RRLib
import Submission.Work.RiemannRoch.RR.mem_WD_sup
import Submission.Work.RiemannRoch.RR.L_eq_bot_of_deg_neg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- Multiplying by the inverse of a nonzero function undoes multiplication by it. -/
theorem smulW_inv_smulW (C : Curve k) {f : C.functionField} (hf : f ≠ 0)
    (ω : WeilDifferential C) : smulW C f⁻¹ (smulW C f ω) = ω := by
  rw [smulW_smul, inv_mul_cancel₀ hf, smulW_one]

/-- `ω ↦ f ω` is additive in `ω`. -/
theorem smulW_neg_right (C : Curve k) (f : C.functionField) (ω : WeilDifferential C) :
    smulW C f (-ω) = -smulW C f ω := by
  ext a; simp [smulW_apply]

/-- `f ↦ f ω` is additive in `f`. -/
theorem smulW_neg_left (C : Curve k) (f : C.functionField) (ω : WeilDifferential C) :
    smulW C (-f) ω = -smulW C f ω := by
  simpa only [smulWLin_apply] using map_neg (smulWLin C ω) f

/-- If `f ∈ L (D - E)` and `ω` vanishes on `K + A(D)`, then `f ω` vanishes on `K + A(E)`.

Indeed `E ≤ D + div f` because `div f + D - E` is effective, and `WD (D + div f) ≤ WD E`
by antitonicity of `WD`. -/
theorem smulW_mem_WD_of_mem_L (C : Curve k) {f : C.functionField} {D E : C.Div}
    (hf : f ∈ C.L (D - E)) {ω : WeilDifferential C} (hω : ω ∈ WD C D) :
    smulW C f ω ∈ WD C E := by
  by_cases hf0 : f = 0
  · rw [hf0, smulW_zero_left]
    exact Submodule.zero_mem _
  · refine WD_anti C ?_ (Work.RiemannRoch.RR.smulW_mem_WD C hf0 hω)
    rw [Finsupp.le_def]
    intro Q
    rw [C.mem_L_iff] at hf
    rcases hf with h0 | hEff
    · exact absurd h0 hf0
    have hq := hEff Q
    simp only [Finsupp.add_apply, Finsupp.sub_apply,
      Work.CurveBasics.Curve.div_apply] at hq
    simp only [Finsupp.add_apply, Work.CurveBasics.Curve.div_apply]
    linarith

/-- **A two-term dimension bound for Weil differentials.**

If `ω, ω' ∈ WD D` and the only relation `f ω + h ω' = 0` in the `k`-vector space of functionals
is the trivial one, then `2 l (D - E) ≤ dim WD E`.  This is the `ι = Fin 2` case of the
counting lemma `sum_l_le_finrank_WD`, proved here directly: the map
`L(D-E) × L(D-E) → WD E`, `(f, h) ↦ f ω + h ω'` is `k`-linear and injective. -/
theorem two_l_le_finrank_WD (C : Curve k) (D : C.Div) (ω ω' : WeilDifferential C) (E : C.Div)
    (hω : ω ∈ WD C D) (hω' : ω' ∈ WD C D)
    (hind : ∀ f h : C.functionField, smulW C f ω + smulW C h ω' = 0 → f = 0 ∧ h = 0) :
    C.l (D - E) + C.l (D - E) ≤ Module.finrank k ↥(WD C E) := by
  have hmem₁ : ∀ f : ↥(C.L (D - E)), smulW C (f : C.functionField) ω ∈ WD C E :=
    fun f => smulW_mem_WD_of_mem_L C f.2 hω
  have hmem₂ : ∀ f : ↥(C.L (D - E)), smulW C (f : C.functionField) ω' ∈ WD C E :=
    fun f => smulW_mem_WD_of_mem_L C f.2 hω'
  let φ₁ : ↥(C.L (D - E)) →ₗ[k] ↥(WD C E) :=
    LinearMap.codRestrict (WD C E) ((smulWLin C ω).comp (C.L (D - E)).subtype) hmem₁
  let φ₂ : ↥(C.L (D - E)) →ₗ[k] ↥(WD C E) :=
    LinearMap.codRestrict (WD C E) ((smulWLin C ω').comp (C.L (D - E)).subtype) hmem₂
  let φ : (↥(C.L (D - E)) × ↥(C.L (D - E))) →ₗ[k] ↥(WD C E) := φ₁.coprod φ₂
  have hφ : ∀ x, (φ x : WeilDifferential C) =
      smulW C (x.1 : C.functionField) ω + smulW C (x.2 : C.functionField) ω' := by
    intro x
    have hv : ((φ₁ x.1 : ↥(WD C E)) : WeilDifferential C)
        = smulW C (x.1 : C.functionField) ω :=
      LinearMap.codRestrict_apply (WD C E)
        ((smulWLin C ω).comp (C.L (D - E)).subtype) x.1
    have hv' : ((φ₂ x.2 : ↥(WD C E)) : WeilDifferential C)
        = smulW C (x.2 : C.functionField) ω' :=
      LinearMap.codRestrict_apply (WD C E)
        ((smulWLin C ω').comp (C.L (D - E)).subtype) x.2
    calc (φ x : WeilDifferential C)
        = ((φ₁ x.1 : ↥(WD C E)) : WeilDifferential C)
            + ((φ₂ x.2 : ↥(WD C E)) : WeilDifferential C) := by
          rw [LinearMap.coprod_apply, Submodule.coe_add]
      _ = smulW C (x.1 : C.functionField) ω + smulW C (x.2 : C.functionField) ω' := by
          rw [hv, hv']
  have hker : ∀ x, φ x = 0 → x = 0 := by
    intro x hx
    have hx' : smulW C (x.1 : C.functionField) ω + smulW C (x.2 : C.functionField) ω' = 0 := by
      have h := congrArg (Subtype.val) hx
      rw [hφ x, ZeroMemClass.coe_zero] at h
      exact h
    obtain ⟨h1, h2⟩ := hind x.1 x.2 hx'
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hz : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h := hker (x - y) hz
    exact sub_eq_zero.mp h
  have hfin : Module.finrank k (↥(C.L (D - E)) × ↥(C.L (D - E)))
      ≤ Module.finrank k ↥(WD C E) := by
    haveI : Module.Finite k ↥(WD C E) := by
      haveI : Module.Finite k (Module.Dual k (H1 C E)) := inferInstance
      exact Module.Finite.equiv (WDequiv C E)
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have hprod : Module.finrank k (↥(C.L (D - E)) × ↥(C.L (D - E)))
      = C.l (D - E) + C.l (D - E) := by
    rw [Module.finrank_prod]
    rfl
  rwa [hprod] at hfin

end

end Curve

namespace Duality

/-- **The space of Weil differentials is one-dimensional over the function field.**  For any
nonzero `ω ∈ Ω` and any `ω' ∈ Ω` there is `f ∈ K(C)` with `ω' = f ω`.

This is Serre, *Algebraic Groups and Class Fields*, II §8: choosing `D` with `ω, ω' ∈ WD D`, if
`ω'` were not a `K`-multiple of `ω` then `(f, h) ↦ f ω + h ω'` would inject `L(D - Δ_m)²` into
`WD Δ_m` for a large multiple `Δ_m = m [P]` of a place `P`.  Comparing with Riemann–Roch gives
`2(m deg P + 1 - g) ≤ m deg P - deg D - 1 + g` for every `m`, a contradiction. -/
theorem exists_smulW_eq {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    {ω ω' : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)}
    (hω : ω ∈ Work.RiemannRoch.Curve.Omega C) (hω0 : ω ≠ 0)
    (hω' : ω' ∈ Work.RiemannRoch.Curve.Omega C) :
    ∃ f : C.functionField, ω' = Work.RiemannRoch.Curve.smulW C f ω := by
  classical
  by_contra hcon
  push Not at hcon
  -- Choose a divisor `D` with `ω, ω' ∈ WD D`.
  obtain ⟨D₁, hD₁⟩ := Work.RiemannRoch.Curve.mem_Omega_iff.mp hω
  obtain ⟨D₂, hD₂⟩ := Work.RiemannRoch.Curve.mem_Omega_iff.mp hω'
  set D : C.Div := D₁ ⊓ D₂ with hDdef
  have hωD : ω ∈ Work.RiemannRoch.Curve.WD C D := by
    rw [hDdef]
    exact (Work.RiemannRoch.Curve.WD_anti C inf_le_left) hD₁
  have hω'D : ω' ∈ Work.RiemannRoch.Curve.WD C D := by
    rw [hDdef]
    exact (Work.RiemannRoch.Curve.WD_anti C inf_le_right) hD₂
  -- A place `P`.
  obtain ⟨P⟩ := Work.RiemannRoch.Curve.nonempty_place C
  have hdP : (1 : ℤ) ≤ (P.degree : ℤ) := by
    have h : 0 < P.degree := Work.CurveBasics.Place.residueDegree_pos P
    have h' : 1 ≤ P.degree := h
    exact_mod_cast h'
  -- A large multiple `Δ = m [P]`.
  obtain ⟨m, hm⟩ : ∃ m : ℕ,
      (3 * (Work.RiemannRoch.Curve.genus C : ℤ) - 3 - C.deg D) < (m : ℤ) ∧
      C.deg D < (m : ℤ) := by
    obtain ⟨m, hm⟩ := exists_nat_gt
      (max (3 * (Work.RiemannRoch.Curve.genus C : ℤ) - 3 - C.deg D) (C.deg D))
    exact ⟨m, lt_of_le_of_lt (le_max_left _ _) hm, lt_of_le_of_lt (le_max_right _ _) hm⟩
  set Δ : C.Div := m • Work.CurveBasics.Curve.Div.place P with hΔdef
  set E : C.Div := D - Δ with hEdef
  have hDE : D - E = Δ := by rw [hEdef, sub_sub_cancel]
  -- Degree of `Δ`.
  have hdegΔ : C.deg Δ = (m : ℤ) * (P.degree : ℤ) := by
    rw [hΔdef, C.deg_nsmul, C.deg_place]
    simp
  -- The injectivity of `(f, h) ↦ f ω + h ω'`.
  have hind : ∀ f h : C.functionField,
      Work.RiemannRoch.Curve.smulW C f ω + Work.RiemannRoch.Curve.smulW C h ω' = 0 →
      f = 0 ∧ h = 0 := by
    intro f h hfh
    have hcancel : ∀ a : C.functionField, a ≠ 0 → ∀ ξ,
        Work.RiemannRoch.Curve.smulW C a⁻¹ (Work.RiemannRoch.Curve.smulW C a ξ) = ξ :=
      fun a ha ξ => Work.RiemannRoch.Curve.smulW_inv_smulW C ha ξ
    have hnegR : ∀ (a : C.functionField) (ξ),
        Work.RiemannRoch.Curve.smulW C a (-ξ) = -Work.RiemannRoch.Curve.smulW C a ξ :=
      fun a ξ => Work.RiemannRoch.Curve.smulW_neg_right C a ξ
    have hnegL : ∀ (a : C.functionField) (ξ),
        Work.RiemannRoch.Curve.smulW C (-a) ξ = -Work.RiemannRoch.Curve.smulW C a ξ :=
      fun a ξ => Work.RiemannRoch.Curve.smulW_neg_left C a ξ
    constructor
    · by_contra hf0
      have h1 : Work.RiemannRoch.Curve.smulW C f ω
          = -Work.RiemannRoch.Curve.smulW C h ω' :=
        eq_neg_of_add_eq_zero_left hfh
      have h2 : ω = -Work.RiemannRoch.Curve.smulW C (f⁻¹ * h) ω' := by
        have key := congrArg (fun x => Work.RiemannRoch.Curve.smulW C f⁻¹ x) h1
        rw [hcancel f hf0 ω, hnegR, Work.RiemannRoch.Curve.smulW_smul] at key
        exact key
      have hg0 : f⁻¹ * h ≠ 0 := by
        intro hz
        exact hω0 (by rw [h2, hz, Work.RiemannRoch.Curve.smulW_zero_left, neg_zero])
      have h3 : ω' = Work.RiemannRoch.Curve.smulW C (-(f⁻¹ * h)⁻¹) ω := by
        have key := congrArg (fun x => Work.RiemannRoch.Curve.smulW C (f⁻¹ * h)⁻¹ x) h2
        rw [hnegR, Work.RiemannRoch.Curve.smulW_smul, inv_mul_cancel₀ hg0,
          Work.RiemannRoch.Curve.smulW_one] at key
        have hkey : -Work.RiemannRoch.Curve.smulW C (f⁻¹ * h)⁻¹ ω = ω' :=
          neg_eq_iff_eq_neg.mpr key
        rw [← hnegL] at hkey
        exact hkey.symm
      exact hcon (-(f⁻¹ * h)⁻¹) h3
    · by_contra hh0
      have h1 : Work.RiemannRoch.Curve.smulW C h ω'
          = -Work.RiemannRoch.Curve.smulW C f ω :=
        eq_neg_of_add_eq_zero_right hfh
      have h3 : ω' = Work.RiemannRoch.Curve.smulW C (-(h⁻¹ * f)) ω := by
        have key := congrArg (fun x => Work.RiemannRoch.Curve.smulW C h⁻¹ x) h1
        rw [hcancel h hh0 ω', hnegR, Work.RiemannRoch.Curve.smulW_smul] at key
        rw [← hnegL] at key
        exact key
      exact hcon (-(h⁻¹ * f)) h3
  -- The dimension inequality.
  have hmain := Work.RiemannRoch.Curve.two_l_le_finrank_WD C D ω ω' E hωD hω'D hind
  rw [hDE] at hmain
  rw [Work.RiemannRoch.Duality.finrank_WD C E] at hmain
  -- `deg E < 0`, hence `l E = 0`.
  have hdegE : C.deg E < 0 := by
    rw [hEdef, C.deg_sub, hdegΔ]
    have hdD : C.deg D < (m : ℤ) * (P.degree : ℤ) := by
      have hcast : ((m : ℕ) : ℤ) ≤ (m : ℤ) * (P.degree : ℤ) := by
        calc ((m : ℕ) : ℤ) = (m : ℤ) * 1 := by ring
          _ ≤ (m : ℤ) * (P.degree : ℤ) :=
              mul_le_mul_of_nonneg_left hdP (Int.natCast_nonneg m)
      linarith [hm.2]
    linarith
  have hlE : C.l E = 0 := by
    have hbot : C.L E = ⊥ := Work.RiemannRoch.RR.L_eq_bot_of_deg_neg C hdegE
    change Module.finrank k ↥(C.L E) = 0
    rw [hbot]; simp
  have hiE : (Work.RiemannRoch.Curve.i C E : ℤ)
      = -C.deg E - 1 + (Work.RiemannRoch.Curve.genus C : ℤ) := by
    have hrr := Work.RiemannRoch.Curve.riemannRoch C E
    have hl0 : (C.l E : ℤ) = 0 := by rw [hlE]; norm_num
    rw [hl0] at hrr
    linarith
  -- Combine.
  have hlow : 2 * ((m : ℤ) * (P.degree : ℤ) + 1 - (Work.RiemannRoch.Curve.genus C : ℤ))
      ≤ (Work.RiemannRoch.Curve.i C E : ℤ) := by
    have hcast : (C.l Δ : ℤ) + (C.l Δ : ℤ) ≤ (Work.RiemannRoch.Curve.i C E : ℤ) := by
      exact_mod_cast hmain
    have hriem : C.deg Δ + 1 - (Work.RiemannRoch.Curve.genus C : ℤ) ≤ (C.l Δ : ℤ) :=
      Work.RiemannRoch.Curve.riemann_inequality C Δ
    rw [hdegΔ] at hriem
    linarith
  rw [hiE] at hlow
  rw [hEdef, C.deg_sub, hdegΔ] at hlow
  have hmdP : 3 * (Work.RiemannRoch.Curve.genus C : ℤ) - 3 - C.deg D
      < (m : ℤ) * (P.degree : ℤ) := by
    have hcast : ((m : ℕ) : ℤ) ≤ (m : ℤ) * (P.degree : ℤ) := by
      calc ((m : ℕ) : ℤ) = (m : ℤ) * 1 := by ring
        _ ≤ (m : ℤ) * (P.degree : ℤ) :=
            mul_le_mul_of_nonneg_left hdP (Int.natCast_nonneg m)
    linarith [hm.1]
  linarith

end Duality

end Work.RiemannRoch
