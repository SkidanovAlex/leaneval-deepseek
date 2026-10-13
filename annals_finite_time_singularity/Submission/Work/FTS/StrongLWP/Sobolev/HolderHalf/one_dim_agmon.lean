import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

open MeasureTheory

/-- **One-dimensional Agmon inequality.**
For a `C¹` function `f : ℝ → ℝ` with compact support and every `y : ℝ`,
`(f y) ^ 2 ≤ 2 * √(∫ f²) * √(∫ (f')²)`.

Proof: since `f` is `C¹` with compact support, the fundamental theorem of calculus applied to
`f²` on `(-∞, y]` (this is `HasCompactSupport.integral_Iic_deriv_eq`) gives
`(f y) ^ 2 = ∫_{Iic y} 2 f f'`, and Cauchy–Schwarz for `L²` bounds the integral of `f f'` by
`√(∫_{Iic y} f²) √(∫_{Iic y} (f')²)`, which is at most `√(∫ f²) √(∫ (f')²)`. -/
theorem one_dim_agmon {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∀ y : ℝ, (f y) ^ 2 ≤ 2 * Real.sqrt (∫ x : ℝ, (f x) ^ 2) * Real.sqrt (∫ x : ℝ, (deriv f x) ^ 2) := by
  intro y
  -- `f ^ 2` and `(f') ^ 2` have compact support
  have hsq_supp : HasCompactSupport (fun x => f x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hdsq_supp : HasCompactSupport (fun x => deriv f x ^ 2) :=
    hc.deriv.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  -- Fundamental theorem of calculus on `(-∞, y]`
  have hFTC : (f y) ^ 2 = ∫ x in Set.Iic y, 2 * f x * deriv f x := by
    have hF := HasCompactSupport.integral_Iic_deriv_eq (hf.pow 2) hsq_supp y
    rw [← hF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hd : HasDerivAt (fun x => f x ^ 2) (2 * f x * deriv f x) x := by
      have h : HasDerivAt f (deriv f x) x := (hf.differentiable one_ne_zero x).hasDerivAt
      convert h.pow 2 using 1
      ring
    exact hd.deriv
  -- Cauchy–Schwarz on `(-∞, y]`
  have hCS : |∫ x in Set.Iic y, f x * deriv f x| ≤
      Real.sqrt (∫ x in Set.Iic y, (f x) ^ 2) *
        Real.sqrt (∫ x in Set.Iic y, (deriv f x) ^ 2) := by
    have hmem_f : MemLp f 2 (volume.restrict (Set.Iic y)) :=
      (hf.continuous.memLp_of_hasCompactSupport hc).restrict _
    have hmem_d : MemLp (deriv f) 2 (volume.restrict (Set.Iic y)) :=
      ((hf.continuous_deriv le_rfl).memLp_of_hasCompactSupport hc.deriv).restrict _
    have hCS := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict (Set.Iic y))
        (p := 2) (q := 2) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
        (by simpa using hmem_f) (by simpa using hmem_d)
    have h1 : |∫ x in Set.Iic y, f x * deriv f x| ≤
        ∫ x, ‖f x‖ * ‖deriv f x‖ ∂(volume.restrict (Set.Iic y)) := by
      have hEq : (∫ x, |f x * deriv f x| ∂(volume.restrict (Set.Iic y)))
          = ∫ x, ‖f x‖ * ‖deriv f x‖ ∂(volume.restrict (Set.Iic y)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          simp only [Real.norm_eq_abs, abs_mul])
      rw [← hEq]
      exact MeasureTheory.abs_integral_le_integral_abs
    have hpowf : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume.restrict (Set.Iic y))) =
        ∫ x in Set.Iic y, (f x) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs])
    have hpowd : (∫ x, ‖deriv f x‖ ^ (2 : ℝ) ∂(volume.restrict (Set.Iic y))) =
        ∫ x in Set.Iic y, (deriv f x) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs])
    calc |∫ x in Set.Iic y, f x * deriv f x|
        ≤ ∫ x, ‖f x‖ * ‖deriv f x‖ ∂(volume.restrict (Set.Iic y)) := h1
      _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume.restrict (Set.Iic y))) ^ (1 / 2) *
            (∫ x, ‖deriv f x‖ ^ (2 : ℝ) ∂(volume.restrict (Set.Iic y))) ^ (1 / 2) := hCS
      _ = Real.sqrt (∫ x in Set.Iic y, (f x) ^ 2) *
            Real.sqrt (∫ x in Set.Iic y, (deriv f x) ^ 2) := by
          rw [hpowf, hpowd, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  -- monotonicity of the set integrals (the integrands are nonnegative and integrable)
  have hmono_f : (∫ x in Set.Iic y, (f x) ^ 2) ≤ ∫ x : ℝ, (f x) ^ 2 := by
    refine MeasureTheory.setIntegral_le_integral ?_ ?_
    · exact (hf.continuous.pow 2).integrable_of_hasCompactSupport hsq_supp
    · filter_upwards with x
      positivity
  have hmono_d : (∫ x in Set.Iic y, (deriv f x) ^ 2) ≤ ∫ x : ℝ, (deriv f x) ^ 2 := by
    refine MeasureTheory.setIntegral_le_integral ?_ ?_
    · exact ((hf.continuous_deriv le_rfl).pow 2).integrable_of_hasCompactSupport hdsq_supp
    · filter_upwards with x
      positivity
  -- pull the constant `2` out of the integral
  have hfac : (∫ x in Set.Iic y, 2 * f x * deriv f x) =
      2 * ∫ x in Set.Iic y, f x * deriv f x := by
    have hfun : (fun x => 2 * f x * deriv f x) = fun x => 2 * (f x * deriv f x) := by
      funext x; ring
    rw [hfun, MeasureTheory.integral_const_mul]
  calc (f y) ^ 2 = ∫ x in Set.Iic y, 2 * f x * deriv f x := hFTC
    _ = 2 * ∫ x in Set.Iic y, f x * deriv f x := hfac
    _ ≤ |2 * ∫ x in Set.Iic y, f x * deriv f x| := le_abs_self _
    _ = 2 * |∫ x in Set.Iic y, f x * deriv f x| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * (Real.sqrt (∫ x in Set.Iic y, (f x) ^ 2) *
          Real.sqrt (∫ x in Set.Iic y, (deriv f x) ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS (by norm_num)
    _ ≤ 2 * (Real.sqrt (∫ x : ℝ, (f x) ^ 2) * Real.sqrt (∫ x : ℝ, (deriv f x) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt hmono_f)
          (Real.sqrt_le_sqrt hmono_d) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by norm_num)
    _ = 2 * Real.sqrt (∫ x : ℝ, (f x) ^ 2) * Real.sqrt (∫ x : ℝ, (deriv f x) ^ 2) := by ring

end Work.FTS.StrongLWP.Sobolev.HolderHalf
