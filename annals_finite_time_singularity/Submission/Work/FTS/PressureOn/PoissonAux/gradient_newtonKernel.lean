import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.PoissonAux

open Work.FTS.PressureOn

/-! ## Two derivatives on `ℝ³`

Everything is done through Fréchet derivatives, since `gradient` is *defined* as the Riesz
representative of `fderiv`.  The two ingredients are

* `∇‖·‖ z = ‖z‖⁻¹ • z` at `z ≠ 0` (`hasFDerivAt_norm_R3`); and
* the inverse rule, giving `∇(‖·‖⁻¹) z = -(‖z‖²)⁻¹‖z‖⁻¹ • z` (`hasFDerivAt_inv_norm_R3`).

The Newtonian kernel `(4π‖z‖)⁻¹` is `(4π)⁻¹ * ‖z‖⁻¹`, so the chain rule gives the stated
gradient.  At `z = 0` the kernel is *not* differentiable (its value there is `0` but it blows
up nearby), so there both sides are `0` for the junk-value reasons built into `fderiv`. -/

/-- The Fréchet derivative of the norm on `ℝ³` at a nonzero point: since `‖·‖ = √(‖·‖²)` and
`fderiv (‖·‖²) z = 2 ⟪z, ·⟫`, the derivative is `⟪‖z‖⁻¹ • z, ·⟫`. -/
private lemma hasFDerivAt_norm_R3 (z : R3) (hz : z ≠ 0) :
    HasFDerivAt (fun x : R3 => ‖x‖) (innerSL ℝ (‖z‖⁻¹ • z)) z := by
  have hz' : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
  have hsq : HasFDerivAt (fun x : R3 => ‖x‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt (‖z‖ ^ 2)))
      (‖z‖ ^ 2) :=
    Real.hasDerivAt_sqrt (pow_ne_zero 2 hz')
  have hcomp : HasFDerivAt (fun x : R3 => Real.sqrt (‖x‖ ^ 2))
      ((ContinuousLinearMap.toSpanSingleton ℝ (1 / (2 * Real.sqrt (‖z‖ ^ 2))))
        ∘SL (2 • innerSL ℝ z)) z :=
    hsqrt.hasFDerivAt.comp z hsq
  have heq : (fun x : R3 => Real.sqrt (‖x‖ ^ 2)) = fun x => ‖x‖ := by
    funext x; exact Real.sqrt_sq (norm_nonneg x)
  rw [heq] at hcomp
  convert hcomp using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_apply, smul_eq_mul, innerSL_apply_apply, Real.sqrt_sq (norm_nonneg z),
    real_inner_smul_left]
  field_simp
  ring

/-- The Fréchet derivative of `‖·‖⁻¹` at a nonzero point, by the inverse rule applied to the
norm: `∇(‖·‖⁻¹) z = -(‖z‖²)⁻¹ • ∇‖·‖ z`. -/
private lemma hasFDerivAt_inv_norm_R3 (z : R3) (hz : z ≠ 0) :
    HasFDerivAt (fun x : R3 => ‖x‖⁻¹)
      (innerSL ℝ (( -(‖z‖ ^ 2)⁻¹ * ‖z‖⁻¹) • z)) z := by
  have hz' : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnorm := hasFDerivAt_norm_R3 z hz
  have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-(‖z‖ ^ 2)⁻¹) (‖z‖) := hasDerivAt_inv hz'
  have hcomp : HasFDerivAt (fun x : R3 => ‖x‖⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(‖z‖ ^ 2)⁻¹))
        ∘SL (innerSL ℝ (‖z‖⁻¹ • z))) z :=
    hinv.hasFDerivAt.comp z hnorm
  convert hcomp using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, innerSL_apply_apply, real_inner_smul_left]
  ring

/-- The Newtonian kernel is not differentiable at the origin: it vanishes there but blows up
along any ray.  Hence its `gradient` there is the junk value `0`. -/
private lemma not_differentiableAt_newtonKernel_zero :
    ¬ DifferentiableAt ℝ newtonKernel 0 := by
  intro hd
  have hct : ContinuousAt newtonKernel 0 := hd.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hct 1 (by norm_num)
  have hk0 : newtonKernel 0 = 0 := by simp [newtonKernel]
  -- a point of small norm at which the kernel is large
  set r : ℝ := min δ 1 / (8 * Real.pi) with hrdef
  have h8pi : (1 : ℝ) < 8 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hrlt : r < δ := by
    rw [hrdef]
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right (min_le_left δ 1) (by positivity)) ?_
    exact div_lt_self hδpos h8pi
  have henorm : ‖(FiniteTimeSingularity.e 0 : R3)‖ = 1 := by simp [FiniteTimeSingularity.e]
  set y : R3 := r • (FiniteTimeSingularity.e 0) with hydef
  have hyval : newtonKernel y = (4 * Real.pi * r)⁻¹ := by
    rw [hydef, newtonKernel, norm_smul, henorm, mul_one, Real.norm_eq_abs, abs_of_pos hrpos]
  have hyball : y ∈ Metric.ball (0 : R3) δ := by
    rw [Metric.mem_ball, dist_zero_right, hydef, norm_smul, henorm, mul_one,
      Real.norm_eq_abs, abs_of_pos hrpos]
    exact hrlt
  have hb := hδ hyball
  rw [hk0, dist_zero_right, Real.norm_eq_abs] at hb
  -- the kernel is at least `2` there
  have h4 : 4 * Real.pi * r ≤ 1 / 2 := by
    rw [hrdef]
    have : 4 * Real.pi * (min δ 1 / (8 * Real.pi)) = min δ 1 / 2 := by field_simp; ring
    rw [this]; linarith [min_le_right δ 1]
  have hpos4 : 0 < 4 * Real.pi * r := by positivity
  have hge : (2 : ℝ) ≤ newtonKernel y := by
    rw [hyval]
    have hh := inv_anti₀ hpos4 h4
    have h2 : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
    rw [h2] at hh
    exact hh
  have hb1 : newtonKernel y < 1 := (abs_lt.mp hb).2
  linarith

/-- The gradient of the Newtonian kernel `newtonKernel z = (4π‖z‖)⁻¹`
(`Work.FTS.PressureOn.newtonKernel`, `Submission/Work/FTS/PressureOn/Defs.lean`) is the
explicitly defined `newtonGrad z = -((4π)⁻¹‖z‖⁻³) • z` (`Work.FTS.PressureOn.newtonGrad`),
pointwise on all of `ℝ³` (both sides are `0` at `z = 0`). -/
theorem gradient_newtonKernel (z : Work.FTS.PressureOn.R3) :
    gradient Work.FTS.PressureOn.newtonKernel z = Work.FTS.PressureOn.newtonGrad z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [gradient_eq_zero_of_not_differentiableAt (f := newtonKernel)]
    · rw [newtonGrad_apply]; simp
    · exact not_differentiableAt_newtonKernel_zero
  · -- `z ≠ 0`: the chain rule, the inverse rule and the scaling `(4π‖z‖)⁻¹ = (4π)⁻¹‖z‖⁻¹`
    have hbase := hasFDerivAt_inv_norm_R3 z hz
    have hc : HasFDerivAt (fun x : R3 => (4 * Real.pi)⁻¹ * ‖x‖⁻¹)
        ((4 * Real.pi)⁻¹ • innerSL ℝ (( -(‖z‖ ^ 2)⁻¹ * ‖z‖⁻¹) • z)) z :=
      hbase.const_mul ((4 * Real.pi)⁻¹)
    have hnewt : HasFDerivAt newtonKernel
        ((4 * Real.pi)⁻¹ • innerSL ℝ (( -(‖z‖ ^ 2)⁻¹ * ‖z‖⁻¹) • z)) z := by
      have hfun : newtonKernel = fun x : R3 => (4 * Real.pi)⁻¹ * ‖x‖⁻¹ := by
        funext x; rw [newtonKernel]; ring
      rw [hfun]
      exact hc
    -- the Riesz representative of this derivative is exactly `newtonGrad z`
    have hmap : ((4 * Real.pi)⁻¹ • innerSL ℝ (( -(‖z‖ ^ 2)⁻¹ * ‖z‖⁻¹) • z))
        = InnerProductSpace.toDual ℝ R3 (newtonGrad z) := by
      ext v
      rw [newtonGrad_apply]
      simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
        real_inner_smul_left, InnerProductSpace.toDual_apply_apply]
      have hz' : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
      field_simp
    have h := hnewt.hasGradientAt.gradient
    rw [hmap] at h
    rw [h, LinearIsometryEquiv.symm_apply_apply]

end Work.FTS.PressureOn.PoissonAux
