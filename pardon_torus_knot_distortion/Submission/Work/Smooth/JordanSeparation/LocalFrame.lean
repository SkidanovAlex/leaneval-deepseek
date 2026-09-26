import Mathlib
import Submission.Work.Smooth.JordanSeparation.SimpleCurves

/-!
# The local frame of a curve at a regular point

At a parameter `0` where `deriv c.γ 0 ≠ 0` the curve has a well-defined unit tangent
`locE c = γ'(0)/‖γ'(0)‖` and unit normal `locN c = I·locE c`.  Dividing the vector `z - γ(0)` by
the unit complex number `locE c` decomposes it into coordinates `locX c z` (along the tangent) and
`locY c z` (along the normal); this file records the elementary algebra of this frame, together
with the derivative of the tangential coordinate along the curve.  It is the coordinate system in
which the two local sides of the curve at `γ 0` are described (`LocalSides.lean`).
-/

open Set Metric
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- The **unit tangent** of `c` at the parameter `0`. -/
def locE (c : SmoothPlaneCurve) : ℂ := deriv c.γ 0 / ((‖deriv c.γ 0‖ : ℝ) : ℂ)

/-- The **unit normal** of `c` at the parameter `0`. -/
def locN (c : SmoothPlaneCurve) : ℂ := Complex.I * locE c

/-- The coordinate of `z - γ 0` in the unit-tangent direction, as a complex number. -/
def locZ (c : SmoothPlaneCurve) (z : ℂ) : ℂ := (z - c.γ 0) / locE c

/-- The tangential coordinate of `z` in the frame at `γ 0`. -/
def locX (c : SmoothPlaneCurve) (z : ℂ) : ℝ := (locZ c z).re

/-- The normal coordinate of `z` in the frame at `γ 0`. -/
def locY (c : SmoothPlaneCurve) (z : ℂ) : ℝ := (locZ c z).im

/-- The tangential coordinate of the curve point `γ t`. -/
def locS (c : SmoothPlaneCurve) (t : ℝ) : ℝ := locX c (c.γ t)

/-- The normal coordinate of the curve point `γ t`. -/
def locR (c : SmoothPlaneCurve) (t : ℝ) : ℝ := locY c (c.γ t)

/-- The **local parametrisation**: `(t,u) ↦ γ t + u·locN c`. -/
def locPhi (c : SmoothPlaneCurve) (p : ℝ × ℝ) : ℂ := c.γ p.1 + (p.2 : ℂ) * locN c

theorem locE_eq (c : SmoothPlaneCurve) :
    locE c = deriv c.γ 0 / ((‖deriv c.γ 0‖ : ℝ) : ℂ) := rfl

theorem norm_locE (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) : ‖locE c‖ = 1 := by
  rw [locE, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg (deriv c.γ 0))]
  exact div_self (norm_ne_zero_iff.mpr hreg)

theorem locE_ne_zero (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) : locE c ≠ 0 := by
  intro h
  have := norm_locE c hreg
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

theorem deriv_eq_norm_smul_locE (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) :
    deriv c.γ 0 = ((‖deriv c.γ 0‖ : ℝ) : ℂ) * locE c := by
  have hA : ((‖deriv c.γ 0‖ : ℝ) : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_eq_zero] using norm_ne_zero_iff.mpr hreg
  rw [locE]
  exact (mul_div_cancel₀ (deriv c.γ 0) hA).symm

theorem div_locE_eq_re (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) :
    deriv c.γ 0 / locE c = ((‖deriv c.γ 0‖ : ℝ) : ℂ) :=
  (div_eq_iff (locE_ne_zero c hreg)).mpr (deriv_eq_norm_smul_locE c hreg)

theorem locZ_mul (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) (z : ℂ) :
    locE c * locZ c z = z - c.γ 0 := by
  rw [locZ]
  exact mul_div_cancel₀ (z - c.γ 0) (locE_ne_zero c hreg)

/-- **Reconstruction of a point from its local coordinates.** -/
theorem loc_reconstruction (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) (z : ℂ) :
    z = c.γ 0 + (locX c z : ℂ) * locE c + (locY c z : ℂ) * locN c := by
  have h : locZ c z = (locX c z : ℂ) + (locY c z : ℂ) * Complex.I := by
    rw [locX, locY]
    exact (Complex.re_add_im (locZ c z)).symm
  calc z = c.γ 0 + (z - c.γ 0) := by ring
    _ = c.γ 0 + locE c * ((locX c z : ℂ) + (locY c z : ℂ) * Complex.I) := by
          rw [← locZ_mul c hreg z, h]
    _ = c.γ 0 + (locX c z : ℂ) * locE c + (locY c z : ℂ) * locN c := by
          rw [locN]; ring

@[simp] theorem locX_self (c : SmoothPlaneCurve) : locX c (c.γ 0) = 0 := by
  simp [locX, locZ]

@[simp] theorem locY_self (c : SmoothPlaneCurve) : locY c (c.γ 0) = 0 := by
  simp [locY, locZ]

@[simp] theorem locS_zero (c : SmoothPlaneCurve) : locS c 0 = 0 := by simp [locS]

@[simp] theorem locR_zero (c : SmoothPlaneCurve) : locR c 0 = 0 := by simp [locR]

theorem locZ_phi (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) (p : ℝ × ℝ) :
    locZ c (locPhi c p) = locZ c (c.γ p.1) + (p.2 : ℂ) * Complex.I := by
  refine mul_left_cancel₀ (locE_ne_zero c hreg) ?_
  rw [locPhi, locN, mul_add, locZ_mul c hreg, locZ_mul c hreg]
  ring

theorem locX_phi (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) (p : ℝ × ℝ) :
    locX c (locPhi c p) = locS c p.1 := by
  have h := congrArg Complex.re (locZ_phi c hreg p)
  show (locZ c (locPhi c p)).re = (locZ c (c.γ p.1)).re
  simpa [Complex.add_re, Complex.mul_re] using h

theorem locY_phi (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) (p : ℝ × ℝ) :
    locY c (locPhi c p) = locR c p.1 + p.2 := by
  have h := congrArg Complex.im (locZ_phi c hreg p)
  show (locZ c (locPhi c p)).im = (locZ c (c.γ p.1)).im + p.2
  simpa [Complex.add_im, Complex.mul_im] using h

theorem deriv_locS (c : SmoothPlaneCurve) (t : ℝ) :
    deriv (locS c) t = (deriv c.γ t / locE c).re := by
  have hd : HasDerivAt c.γ (deriv c.γ t) t := (c.differentiable t).hasDerivAt
  have hsub : HasDerivAt (fun s : ℝ => c.γ s - c.γ 0) (deriv c.γ t) t := hd.sub_const _
  have hdiv : HasDerivAt (fun s : ℝ => (c.γ s - c.γ 0) / locE c) (deriv c.γ t / locE c) t :=
    hsub.div_const _
  have := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hdiv)
  exact this.deriv

theorem deriv_locS_zero (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) :
    deriv (locS c) 0 = ‖deriv c.γ 0‖ := by
  rw [deriv_locS, div_locE_eq_re c hreg, Complex.ofReal_re]

theorem continuous_deriv_locS (c : SmoothPlaneCurve) : Continuous (deriv (locS c)) := by
  rw [show deriv (locS c) = fun t => (deriv c.γ t / locE c).re from funext (deriv_locS c)]
  exact Complex.continuous_re.comp (c.continuous_deriv.div_const (locE c))

theorem continuous_locX (c : SmoothPlaneCurve) : Continuous (locX c) := by
  rw [show locX c = fun z => ((z - c.γ 0) / locE c).re from rfl]
  exact Complex.continuous_re.comp ((continuous_id.sub continuous_const).div_const (locE c))

theorem continuous_locY (c : SmoothPlaneCurve) : Continuous (locY c) := by
  rw [show locY c = fun z => ((z - c.γ 0) / locE c).im from rfl]
  exact Complex.continuous_im.comp ((continuous_id.sub continuous_const).div_const (locE c))

theorem continuous_locS (c : SmoothPlaneCurve) : Continuous (locS c) := by
  have h : locS c = fun t => ((c.γ t - c.γ 0) / locE c).re := rfl
  rw [show locS c = fun t => ((c.γ t - c.γ 0) / locE c).re from rfl]
  exact Complex.continuous_re.comp ((c.cont.sub continuous_const).div_const (locE c))

theorem continuous_locR (c : SmoothPlaneCurve) : Continuous (locR c) := by
  have h : locR c = fun t => ((c.γ t - c.γ 0) / locE c).im := rfl
  rw [show locR c = fun t => ((c.γ t - c.γ 0) / locE c).im from rfl]
  exact Complex.continuous_im.comp ((c.cont.sub continuous_const).div_const (locE c))

theorem continuous_locPhi (c : SmoothPlaneCurve) :
    Continuous (fun p : ℝ × ℝ => locPhi c p) := by
  rw [show (fun p : ℝ × ℝ => locPhi c p) = fun p => c.γ p.1 + (p.2 : ℂ) * locN c from rfl]
  exact (c.cont.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

end

end Work.Smooth.JordanSeparation
