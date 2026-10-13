import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.ofReal_sliceMass_pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory

namespace Work.FTS.ClassCHon.SliceMassUpgrade

/-- The `τ`-weighted (`τ ≥ 0` arbitrary) pointwise slice-mass comparison: for a source `F`
smooth on the open quadrant, `z₁ ≤ z₂`, `z₁ > 0` and interior `θ`,

  `τ θ · F(z₂,θ)² ≤ 2 τ θ · F(z₁,θ)² + 2 τ θ · (z₂ - z₁) ∫_{z₁}^{z₂} (∂_z F(s,θ))²`.

This is the general form of `ofReal_sliceMass_pointwise` (which is the case `τ = sEta`), with
the angular weight left abstract; the proof is the FTC + Cauchy–Schwarz argument on the
`z`-slice, with no positivity or measurability needed of `τ` beyond `τ ≥ 0` on `Iθ`. -/
theorem ofReal_sliceMass_pointwise_gen {F : ℝ → ℝ → ℝ} {τ : ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hτ : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ τ θ)
    {z₁ z₂ θ : ℝ} (hz₁ : 0 < z₁) (hz₁₂ : z₁ ≤ z₂) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ENNReal.ofReal (τ θ * (F z₂ θ) ^ 2)
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2)
        + ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ)
            * ENNReal.ofReal (z₂ - z₁)
            * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)) := by
  set A : ℝ := τ θ with hAdef
  set I : ℝ := ∫ s in z₁..z₂, Work.Spaces.pz F s θ with hIdef
  set J : ℝ := ∫ s in z₁..z₂, (Work.Spaces.pz F s θ) ^ 2 with hJdef
  -- nonnegativity of the angular weight
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact hτ θ hθ
  have hz2 : 0 ≤ z₂ - z₁ := sub_nonneg.mpr hz₁₂
  -- the slices are smooth on the open half-line, hence on `[z₁,z₂]`
  have hsub : Set.Icc z₁ z₂ ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le hz₁ hs.1
  have hcontf : ContinuousOn (fun s : ℝ => Work.Spaces.pz F s θ) (Set.Icc z₁ z₂) :=
    ((hF.pz.curry_z hθ).continuousOn).mono hsub
  -- fundamental theorem of calculus for the slice
  have hderiv : ∀ s ∈ Set.uIcc z₁ z₂,
      HasDerivAt (fun s' : ℝ => F s' θ) (Work.Spaces.pz F s θ) s := by
    intro s hs
    rw [Set.uIcc_of_le hz₁₂] at hs
    exact hF.hasDerivAt_slice hθ (lt_of_lt_of_le hz₁ hs.1)
  have hint : IntervalIntegrable (fun s : ℝ => Work.Spaces.pz F s θ) volume z₁ z₂ := by
    have hc : ContinuousOn (fun s : ℝ => Work.Spaces.pz F s θ) (Set.uIcc z₁ z₂) := by
      rw [Set.uIcc_of_le hz₁₂]; exact hcontf
    exact hc.intervalIntegrable
  have hftc : F z₂ θ - F z₁ θ = I := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [hIdef]
    exact h.symm
  -- nonnegativity of the squared-gradient slice integral
  have hJ : 0 ≤ J := by
    rw [hJdef]
    exact intervalIntegral.integral_nonneg hz₁₂ (fun u _ => sq_nonneg _)
  -- Cauchy–Schwarz: `I² ≤ (z₂ - z₁) J`
  have hI2 : I ^ 2 ≤ (z₂ - z₁) * J := by
    have h := interval_integral_sq_le_measure_mul hz₁₂ hcontf (g := fun s => Work.Spaces.pz F s θ)
    rw [hIdef, hJdef]
    exact h
  -- the elementary pointwise bound
  have hmain : A * (F z₂ θ) ^ 2 ≤ 2 * (A * (F z₁ θ) ^ 2) + 2 * (A * (z₂ - z₁) * J) := by
    have hb2 : (F z₂ θ) ^ 2 ≤ 2 * (F z₁ θ) ^ 2 + 2 * I ^ 2 := by
      have hb : F z₂ θ = F z₁ θ + I := by linarith [hftc]
      rw [hb]
      nlinarith [sq_nonneg (F z₁ θ - I)]
    have h1 : A * (F z₂ θ) ^ 2 ≤ A * (2 * (F z₁ θ) ^ 2 + 2 * I ^ 2) :=
      mul_le_mul_of_nonneg_left hb2 hA
    have h2 : A * I ^ 2 ≤ A * ((z₂ - z₁) * J) := mul_le_mul_of_nonneg_left hI2 hA
    nlinarith [h1, h2]
  -- convert the angular lintegral into `ofReal J`
  have hcont2 : ContinuousOn (fun s : ℝ => (Work.Spaces.pz F s θ) ^ 2) (Set.Icc z₁ z₂) :=
    hcontf.pow 2
  have hL : (∫⁻ s in Set.Ioo z₁ z₂,
      ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)) = ENNReal.ofReal J := by
    rw [hJdef]
    exact (Work.FTS.EllipticEst.AngSecond.ofReal_intervalIntegral_eq_lintegral hz₁₂ hcont2
      (fun x _ => sq_nonneg _)).symm
  rw [hL]
  have h1 : 0 ≤ 2 * (A * (F z₁ θ) ^ 2) :=
    mul_nonneg (by norm_num) (mul_nonneg hA (sq_nonneg _))
  have h2 : 0 ≤ 2 * (A * (z₂ - z₁) * J) :=
    mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hA hz2) hJ)
  have hEqMul : ENNReal.ofReal (A * (z₂ - z₁) * J)
      = ENNReal.ofReal A * ENNReal.ofReal (z₂ - z₁) * ENNReal.ofReal J := by
    rw [ENNReal.ofReal_mul (mul_nonneg hA hz2), ENNReal.ofReal_mul hA]
  refine le_trans (ENNReal.ofReal_le_ofReal hmain) ?_
  rw [ENNReal.ofReal_add h1 h2, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), hEqMul]

end Work.FTS.ClassCHon.SliceMassUpgrade
