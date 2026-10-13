import Mathlib

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: generic regularity of a shear.

  Let `U ⊆ ℝⁿ` be open, `Λ` a finite-dimensional real normed space, and let
  `A : ℝⁿ → ℝⁿ`, `b : ℝⁿ → (Λ →L ℝⁿ)` be `C¹` on `U`.  Writing
  `F_λ x = A x + b x λ`, we show that for a.e. `q = (y, λ)` (for any additive Haar measure `ν`
  on `ℝⁿ × Λ`), every solution `x ∈ U` of `F_λ x = y` has *injective* differential at `x`.

  This is a Sard-type statement.  Consider the shear (graph) map
  `Φ : ℝⁿ × Λ → ℝⁿ × Λ`, `Φ (x, λ) = (A x + b x λ, λ)`, whose linearisation at `(x, λ)` is
  `(v, w) ↦ (d(A + b·λ)_x v + b x w, w)`.  Its determinant vanishes exactly when the
  `x`-block `d(A + b·λ)_x` is singular: a kernel vector `ξ ≠ 0` of the latter gives the kernel
  vector `(ξ, 0)` of the former.  Hence the set of "bad" values is contained in the image of the
  critical set of `Φ`, and the fixed-dimension Sard lemma
  `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` (Mathlib's
  `MeasureTheory/Function/Jacobian.lean`) makes that image null.
-/

noncomputable section

open scoped Topology
open MeasureTheory

namespace Work.WilE3.Taylor.CaseII

theorem ae_regular_shear {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
    [MeasurableSpace Λ] [BorelSpace Λ]
    (ν : MeasureTheory.Measure ((Fin n → ℝ) × Λ)) [MeasureTheory.Measure.IsAddHaarMeasure ν]
    (A : (Fin n → ℝ) → (Fin n → ℝ))
    (b : (Fin n → ℝ) → Λ →L[ℝ] (Fin n → ℝ))
    (hA : ContDiffOn ℝ 1 A U) (hb : ContDiffOn ℝ 1 b U) :
    ∀ᵐ q ∂ν, ∀ x ∈ U, A x + b x q.2 = q.1 →
        Function.Injective (fderiv ℝ (fun z => A z + b z q.2) x) := by
  -- The shear (graph) map `Φ (x, λ) = (A x + b x λ, λ)` on `ℝⁿ × Λ`.
  set Φ : (Fin n → ℝ) × Λ → (Fin n → ℝ) × Λ :=
    fun u => (A u.1 + b u.1 u.2, u.2) with hΦdef
  -- Its derivative, exhibited explicitly.
  set DΦ : (Fin n → ℝ) × Λ → ((Fin n → ℝ) × Λ) →L[ℝ] ((Fin n → ℝ) × Λ) :=
    fun u => ContinuousLinearMap.prod
      ((fderiv ℝ A u.1).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)
        + ((b u.1).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ)
          + ((fderiv ℝ b u.1).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)).flip u.2))
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ) with hDΦdef
  -- Differentiability of `A` and `b` at points of `U`.
  have hdiff : ∀ u : (Fin n → ℝ) × Λ, u.1 ∈ U →
      HasFDerivAt A (fderiv ℝ A u.1) u.1 ∧ HasFDerivAt b (fderiv ℝ b u.1) u.1 := by
    intro u hu
    exact ⟨((hA.contDiffAt (hU.mem_nhds hu)).differentiableAt one_ne_zero).hasFDerivAt,
           ((hb.contDiffAt (hU.mem_nhds hu)).differentiableAt one_ne_zero).hasFDerivAt⟩
  -- `Φ` is differentiable on `U × univ` with derivative `DΦ`.
  have hfd : ∀ u : (Fin n → ℝ) × Λ, u.1 ∈ U → HasFDerivAt Φ (DΦ u) u := by
    intro u hu
    obtain ⟨hAu, hbu⟩ := hdiff u hu
    have h1 : HasFDerivAt (fun u : (Fin n → ℝ) × Λ => A u.1)
        ((fderiv ℝ A u.1).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)) u :=
      hAu.comp u (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ).hasFDerivAt
    have h2 : HasFDerivAt (fun u : (Fin n → ℝ) × Λ => b u.1)
        ((fderiv ℝ b u.1).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)) u :=
      hbu.comp u (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ).hasFDerivAt
    have h3 : HasFDerivAt (fun u : (Fin n → ℝ) × Λ => b u.1 u.2)
        ((b u.1).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ)
          + ((fderiv ℝ b u.1).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)).flip u.2) u :=
      h2.clm_apply (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ).hasFDerivAt
    have h4 : HasFDerivAt (fun u : (Fin n → ℝ) × Λ => (A u.1 + b u.1 u.2, u.2))
        (ContinuousLinearMap.prod
          ((fderiv ℝ A u.1).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)
            + ((b u.1).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ)
              + ((fderiv ℝ b u.1).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)).flip u.2))
          (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ)) u :=
      (h1.add h3).prodMk (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ).hasFDerivAt
    show HasFDerivAt (fun u : (Fin n → ℝ) × Λ => (A u.1 + b u.1 u.2, u.2))
        (ContinuousLinearMap.prod
          ((fderiv ℝ A u.1).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)
            + ((b u.1).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ)
              + ((fderiv ℝ b u.1).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)).flip u.2))
          (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ)) u
    exact h4
  -- The critical set of `Φ` inside `U × univ`.
  set s : Set ((Fin n → ℝ) × Λ) := {u | u.1 ∈ U ∧ (DΦ u).det = 0} with hsdef
  have hs' : ∀ u ∈ s, HasFDerivWithinAt Φ (DΦ u) s u := by
    intro u hu
    exact (hfd u hu.1).hasFDerivWithinAt
  have hdet' : ∀ u ∈ s, (DΦ u).det = 0 := fun u hu => hu.2
  have hSard : ν (Φ '' s) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero ν hs' hdet'
  -- The criticality criterion: a non-injective `x`-differential makes `(x, λ)` critical for `Φ`.
  have hcrit : ∀ (x : Fin n → ℝ) (lam : Λ), x ∈ U →
      ¬ Function.Injective (fderiv ℝ (fun z => A z + b z lam) x) →
      (DΦ (x, lam)).det = 0 := by
    intro x lam hxU hni
    rw [Function.Injective] at hni
    push_neg at hni
    obtain ⟨a₁, a₂, heq, hne⟩ := hni
    set ξ : Fin n → ℝ := a₁ - a₂ with hξdef
    have hξne : ξ ≠ 0 := by rw [hξdef]; exact sub_ne_zero.mpr hne
    have hMξ : fderiv ℝ (fun z => A z + b z lam) x ξ = 0 := by
      rw [hξdef, map_sub, heq, sub_self]
    obtain ⟨hAu, hbu⟩ := hdiff (x, lam) hxU
    have hbw : HasFDerivAt (fun z => b z lam) ((fderiv ℝ b x).flip lam) x := by
      have h := hbu.clm_apply (hasFDerivAt_const (x := x) lam)
      simpa using h
    have hsum : fderiv ℝ (fun z => A z + b z lam) x
        = fderiv ℝ A x + (fderiv ℝ b x).flip lam := (hAu.add hbw).fderiv
    have hMval : fderiv ℝ (fun z => A z + b z lam) x ξ
        = fderiv ℝ A x ξ + (fderiv ℝ b x).flip lam ξ := by rw [hsum]; rfl
    have hzero : DΦ (x, lam) (ξ, 0) = 0 := by
      show (ContinuousLinearMap.prod
              ((fderiv ℝ A x).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)
                + ((b x).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ)
                  + ((fderiv ℝ b x).comp
                      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)).flip lam))
              (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ)) (ξ, 0) = 0
      have hthis : ((fderiv ℝ A x).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)
            + ((b x).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) Λ)
              + ((fderiv ℝ b x).comp
                  (ContinuousLinearMap.fst ℝ (Fin n → ℝ) Λ)).flip lam)) (ξ, 0)
          = fderiv ℝ A x ξ + (fderiv ℝ b x).flip lam ξ := by
        show (fderiv ℝ A x) ξ + ((b x) (0 : Λ) + ((fderiv ℝ b x) ξ) lam)
            = (fderiv ℝ A x) ξ + ((fderiv ℝ b x) ξ) lam
        rw [map_zero, zero_add]
      rw [ContinuousLinearMap.prod_apply, hthis, ← hMval, hMξ]
      rfl
    have hker : (DΦ (x, lam)).toLinearMap.ker ≠ ⊥ := by
      intro hbot
      have hv : (ξ, 0) ∈ (DΦ (x, lam)).toLinearMap.ker := by
        rw [LinearMap.mem_ker]
        exact hzero
      rw [hbot, Submodule.mem_bot] at hv
      exact hξne (congrArg Prod.fst hv)
    have hdet1 : LinearMap.det (DΦ (x, lam)).toLinearMap = 0 :=
      LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker
    simpa only [ContinuousLinearMap.det] using hdet1
  -- The "bad" set of parameters.
  set B : Set ((Fin n → ℝ) × Λ) :=
    {q | ∃ x ∈ U, A x + b x q.2 = q.1 ∧
      ¬ Function.Injective (fderiv ℝ (fun z => A z + b z q.2) x)} with hBdef
  have hBsub : B ⊆ Φ '' s := by
    rintro q ⟨x, hxU, hF, hni⟩
    refine ⟨(x, q.2), ⟨hxU, hcrit x q.2 hxU hni⟩, ?_⟩
    show Φ (x, q.2) = q
    rw [hΦdef]
    exact Prod.ext hF rfl
  have hBnull : ν B = 0 := measure_mono_null hBsub hSard
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hBnull
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  rw [hBdef]
  simp only [Set.mem_setOf_eq]
  push_neg at hq
  exact hq

end Work.WilE3.Taylor.CaseII
