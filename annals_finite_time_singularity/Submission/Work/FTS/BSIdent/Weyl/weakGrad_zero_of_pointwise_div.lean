import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl

theorem weakGrad_zero_of_pointwise_div {D : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}
    (hDcont : Continuous D)
    (hDdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt D (fderiv ℝ D x) x)
    (hdiv0 : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → FiniteTimeSingularity.div D x = 0)
    {φ : Work.FTS.BSIdent.R3 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφcs : HasCompactSupport φ) :
    ∫ x, inner ℝ (D x) (gradient φ x) = 0 := by
  -- `φ` is differentiable, and so is `φ • D` off the two coordinate planes
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hcont : Continuous (φ • D) := hφ.continuous.smul hDcont
  have hcs : HasCompactSupport (φ • D) := hφcs.smul_right
  have hdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 →
      HasFDerivAt (φ • D) (fderiv ℝ (φ • D) x) x := fun x hx0 hx2 =>
    (hφd.differentiableAt.smul ((hDdiff x hx0 hx2).differentiableAt)).hasFDerivAt
  -- the divergence of `φ • D` is a.e. the integrand, the pointwise part `φ · div D` vanishing
  have hae : (fun y => FiniteTimeSingularity.div (φ • D) y)
      =ᵐ[MeasureTheory.volume] fun y => inner ℝ (D y) (gradient φ y) := by
    filter_upwards [Work.FTS.PressureOn.ae_coord_ne_zero] with y hy
    rw [Work.FTS.PressureOn.div_smul_eq hφd.differentiableAt
      ((hDdiff y hy.1 hy.2).differentiableAt), hdiv0 y hy.1 hy.2, mul_zero, zero_add]
    exact real_inner_comm (D y) (gradient φ y)
  -- `⟪D, ∇φ⟫` is integrable (continuous, compactly supported), hence so is `div (φ • D)`
  have hintD : MeasureTheory.Integrable (fun y => inner ℝ (D y) (gradient φ y)) :=
    Work.FTS.PressureOn.integrable_inner_gradient hDcont hφ hφcs
  have hDivInt : MeasureTheory.Integrable (fun y => FiniteTimeSingularity.div (φ • D) y) :=
    hintD.congr hae.symm
  -- the divergence theorem off the two planes
  have h := Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
    (W := φ • D) hcont hcs hdiff hDivInt
  rw [← MeasureTheory.integral_congr_ae hae]
  exact h

end Work.FTS.BSIdent.Weyl
