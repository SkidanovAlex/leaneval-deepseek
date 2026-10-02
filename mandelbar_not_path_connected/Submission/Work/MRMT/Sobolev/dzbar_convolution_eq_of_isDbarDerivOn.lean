import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Sobolev

open MeasureTheory Complex Function Filter
open scoped Distributions Topology Convolution ENNReal

noncomputable section

/-! ## Two elementary support/regularity helpers (local copies)

These are the only two facts from `Submission.Work.MRMT.QC.dzbar_mollification_eq_zero` that
the argument below needs; they are reproduced here so that this file depends on nothing but
`Mathlib` and the core definitions `Submission.Work.MRMT.Basic`. -/

/-- A continuous compactly supported function times a locally integrable function is
integrable. -/
private theorem integrable_mul_continuous_hasCompactSupport' {f c : ℂ → ℂ}
    (hf : LocallyIntegrable f (volume : Measure ℂ)) (hc : Continuous c)
    (hcs : HasCompactSupport c) : Integrable (fun t => f t * c t) := by
  have hK : IsCompact (tsupport c) := hcs
  have h1 : IntegrableOn f (tsupport c) (volume : Measure ℂ) := hf.integrableOn_isCompact hK
  have h2 : IntegrableOn (fun t => f t * c t) (tsupport c) (volume : Measure ℂ) :=
    h1.mul_continuousOn hc.continuousOn hK
  exact h2.integrable_of_forall_notMem_eq_zero
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])

/-- The Wirtinger `∂̄` chain rule for the reflection `u ↦ z - u`. -/
private theorem dzbar_reflect' {β : ℂ → ℂ} (hβ : Differentiable ℝ β) (z t : ℂ) :
    dzbar (fun u => β (z - u)) t = - dzbar β (z - t) := by
  have hσ : fderiv ℝ (fun u : ℂ => z - u) t = -ContinuousLinearMap.id ℝ ℂ :=
    ((hasFDerivAt_id (𝕜 := ℝ) t).const_sub z).fderiv
  have hσd : DifferentiableAt ℝ (fun u : ℂ => z - u) t :=
    ((hasFDerivAt_id (𝕜 := ℝ) t).const_sub z).differentiableAt
  have hcomp : fderiv ℝ (fun u => β (z - u)) t
      = (fderiv ℝ β (z - t)).comp (fderiv ℝ (fun u : ℂ => z - u) t) := by
    have h1 : (fun u : ℂ => β (z - u)) = β ∘ (fun u : ℂ => z - u) := rfl
    rw [h1, fderiv_comp t (hβ (z - t)) hσd]
  simp only [dzbar]
  rw [hcomp, hσ, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id]
  simp only [neg_apply]
  ring

/-- **The weak `∂̄`-derivative commutes with mollification.**

If `G` is the weak `∂̄`-derivative of `F` on `U` (`IsDbarDerivOn F G U`), `F` is locally
integrable and `ρ` is smooth with compact support, then at every point `z` for which the
reflected support of `ρ` lies in `U` (`∀ t ∈ tsupport ρ, z - t ∈ U`) the `∂̄`-derivative of
the mollification `F ⋆ ρ` equals the mollification `G ⋆ ρ`:

`∂̄ (F ⋆ ρ) z = (G ⋆ ρ) z`.

The proof differentiates the convolution in the smooth factor `ρ` (legitimate because the other
factor is locally integrable) to write `∂̄ (F ⋆ ρ) z = ∫ t, F t * ∂̄ρ (z - t)`; the weak equation
tested against the reflected kernel `u ↦ ρ (z - u)` — a test function supported in `U` by
hypothesis — together with the chain rule `∂̄(ρ ∘ (z - ·)) = -∂̄ρ (z - ·)` converts this into
`∫ t, G t * ρ (z - t) = (G ⋆ ρ) z`. -/
theorem dzbar_convolution_eq_of_isDbarDerivOn {U : Set ℂ} {F G ρ : ℂ → ℂ}
    (hFG : Work.MRMT.IsDbarDerivOn F G U) (hF : MeasureTheory.LocallyIntegrable F)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) {z : ℂ}
    (hz : ∀ t ∈ tsupport ρ, z - t ∈ U) :
    Work.MRMT.dzbar (MeasureTheory.convolution F ρ (ContinuousLinearMap.mul ℝ ℂ) MeasureTheory.volume) z
      = MeasureTheory.convolution G ρ (ContinuousLinearMap.mul ℝ ℂ) MeasureTheory.volume z := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hρdiff : Differentiable ℝ ρ := hρ1.differentiable (by norm_num)
  have hρfdcont : Continuous (fderiv ℝ ρ) := hρ1.continuous_fderiv (by norm_num)
  have hρfdcs : HasCompactSupport (fderiv ℝ ρ) := hρc.fderiv ℝ
  -- ## Step 1: differentiability of the convolution, with an explicit formula for `fderiv`
  have hderiv : HasFDerivAt
      (MeasureTheory.convolution F ρ (ContinuousLinearMap.mul ℝ ℂ) MeasureTheory.volume)
      (MeasureTheory.convolution F (fderiv ℝ ρ)
        ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) MeasureTheory.volume z) z :=
    hρc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hF hρ1 z
  set D : ℂ →L[ℝ] ℂ := MeasureTheory.convolution F (fderiv ℝ ρ)
      ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) MeasureTheory.volume z with hDdef
  have hfderiv : fderiv ℝ
      (MeasureTheory.convolution F ρ (ContinuousLinearMap.mul ℝ ℂ) MeasureTheory.volume) z = D := by
    rw [hDdef]; exact hderiv.fderiv
  -- ## Step 2: unwrap the two directional derivatives of `D`
  have hDv : ∀ v : ℂ, D v = ∫ t, F t * (fderiv ℝ ρ (z - t)) v := by
    intro v
    have h1 : D v = MeasureTheory.convolution F (fun a => fderiv ℝ ρ a v)
        (ContinuousLinearMap.mul ℝ ℂ) MeasureTheory.volume z := by
      rw [hDdef]
      exact convolution_precompR_apply (L := ContinuousLinearMap.mul ℝ ℂ)
        hF hρfdcs hρfdcont z v
    rw [h1, convolution_def]
    apply integral_congr_ae
    filter_upwards with t
    simp only [ContinuousLinearMap.mul_apply']
  -- ## Step 3: `∂̄ (F ⋆ ρ) z = ∫ t, F t * ∂̄ρ (z - t)`
  have hcontσ : Continuous (fun t : ℂ => z - t) := continuous_const.sub continuous_id
  have hcsσ : HasCompactSupport (fun t : ℂ => fderiv ℝ ρ (z - t)) :=
    hρfdcs.comp_homeomorph (Homeomorph.subLeft z)
  have hcontfd : Continuous (fun t : ℂ => (fderiv ℝ ρ (z - t)) 1) :=
    (hρfdcont.comp hcontσ).clm_apply continuous_const
  have hcontfdI : Continuous (fun t : ℂ => (fderiv ℝ ρ (z - t)) Complex.I) :=
    (hρfdcont.comp hcontσ).clm_apply continuous_const
  have hcsfd : HasCompactSupport (fun t : ℂ => (fderiv ℝ ρ (z - t)) 1) :=
    hcsσ.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L 1) (by simp)
  have hcsfdI : HasCompactSupport (fun t : ℂ => (fderiv ℝ ρ (z - t)) Complex.I) :=
    hcsσ.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L Complex.I) (by simp)
  have hIntA : Integrable (fun t => F t * (fderiv ℝ ρ (z - t)) 1) :=
    integrable_mul_continuous_hasCompactSupport' hF hcontfd hcsfd
  have hIntI : Integrable (fun t => F t * (fderiv ℝ ρ (z - t)) Complex.I) :=
    integrable_mul_continuous_hasCompactSupport' hF hcontfdI hcsfdI
  have hDint : (D 1 + Complex.I * D Complex.I) / 2 = ∫ t, F t * dzbar ρ (z - t) := by
    rw [hDv 1, hDv Complex.I]
    have e1 : Complex.I * ∫ t, F t * (fderiv ℝ ρ (z - t)) Complex.I
        = ∫ t, Complex.I * (F t * (fderiv ℝ ρ (z - t)) Complex.I) := by
      rw [integral_const_mul]
    rw [e1, ← integral_add hIntA (hIntI.const_mul Complex.I)]
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards with t
    simp only [dzbar]
    ring
  have hdz : dzbar
      (MeasureTheory.convolution F ρ (ContinuousLinearMap.mul ℝ ℂ) MeasureTheory.volume) z
      = (D 1 + Complex.I * D Complex.I) / 2 := by
    simp only [dzbar]
    rw [hfderiv]
  -- ## Step 4: the weak equation tested against the reflected kernel `u ↦ ρ (z - u)`
  let φ : 𝓓(⊤, ℂ) :=
    { toFun := fun t => ρ (z - t)
      contDiff' := by
        have hσ : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℂ => z - t) := contDiff_const.sub contDiff_id
        exact hρ.comp hσ
      hasCompactSupport' := hρc.comp_homeomorph (Homeomorph.subLeft z)
      tsupport_subset' := fun t _ => by simp }
  have hφts : tsupport (φ : ℂ → ℂ) ⊆ U := by
    have hts : tsupport (φ : ℂ → ℂ) = tsupport (fun t => ρ (z - t)) := rfl
    rw [hts]
    have h2 : (fun t : ℂ => ρ (z - t)) = ρ ∘ ⇑(Homeomorph.subLeft z) := rfl
    rw [h2, tsupport_comp_eq_preimage ρ (Homeomorph.subLeft z)]
    intro t ht
    have ht' : z - t ∈ tsupport ρ := by
      simpa only [Set.mem_preimage, Homeomorph.coe_subLeft] using ht
    have h3 : z - (z - t) ∈ U := hz (z - t) ht'
    rwa [show z - (z - t) = t by ring] at h3
  have hweak : ∫ t, F t * dzbar (fun u => ρ (z - u)) t = - ∫ t, G t * ρ (z - t) := by
    have hh := (hFG.2.2 φ hφts).2.2
    have hφeq : (φ : ℂ → ℂ) = fun u => ρ (z - u) := rfl
    rw [hφeq] at hh
    simpa using hh
  -- ## Step 5: chain rule for the reflection, and assembly
  have hchain : ∫ t, F t * dzbar ρ (z - t) = - ∫ t, F t * dzbar (fun u => ρ (z - u)) t := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with t
    rw [dzbar_reflect' hρdiff z t]
    ring
  have hconvG : MeasureTheory.convolution G ρ (ContinuousLinearMap.mul ℝ ℂ) MeasureTheory.volume z
      = ∫ t, G t * ρ (z - t) := by
    rw [convolution_def]
    apply integral_congr_ae
    filter_upwards with t
    simp only [ContinuousLinearMap.mul_apply']
  have hkey : ∫ t, F t * dzbar ρ (z - t) = ∫ t, G t * ρ (z - t) := by
    rw [hchain, hweak]; ring
  rw [hdz, hDint, hkey]
  exact hconvG.symm

end

end Work.MRMT.Sobolev
