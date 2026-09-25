import Mathlib

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff FourierTransform

/-- The Japanese-bracket weight `(1 + ‖x‖²) ^ (-4/2)` in dimension two matches the square of the
reciprocal weight `(1 + ‖x‖²)⁻¹`.  Exponent identity `-4/2 = -2` combined with
`Real.rpow_neg_eq_inv_rpow`. -/
private lemma rpow_neg_half4 (x : ℝ) : x ^ (-(4:ℝ)/2) = (x⁻¹)^2 := by
  rw [show (-(4:ℝ)/2) = -(2:ℝ) by norm_num, Real.rpow_neg_eq_inv_rpow]
  norm_num

/-- If all polynomial moments of `V : L²(ℂ)` are in `L²`, then `V` is integrable: use
`V = (1+‖ξ‖²)^{-1} · ((1+‖ξ‖²)V)`, the product of two `L²` functions (`hmom 1` supplies the second
factor, `integrable_rpow_neg_one_add_norm_sq` supplies the first; combine with
`MeasureTheory.MemLp.mul`, Hölder triple `2,2,1`). -/
theorem integrable_of_fourier_moments {V : Lp ℂ 2 volume}
    (hmom : ∀ N : ℕ, MemLp (fun ξ : ℂ => (1 + ‖ξ‖ ^ 2) ^ N * V ξ) 2 volume) :
    Integrable (fun ξ : ℂ => V ξ) := by
  rw [← memLp_one_iff_integrable]
  -- The reciprocal Japanese-bracket weight `(1+‖ξ‖²)⁻¹` is square-integrable on `ℂ` (dimension 2):
  -- its square is `(1+‖ξ‖²)^(-4/2)`, integrable because the exponent exceeds the dimension.
  have hφ : MemLp (fun ξ : ℂ => ((1 + ‖ξ‖ ^ 2 : ℝ))⁻¹) 2 volume := by
    have hmeas : AEStronglyMeasurable (fun ξ : ℂ => ((1 + ‖ξ‖ ^ 2 : ℝ))⁻¹) volume := by
      apply Measurable.aestronglyMeasurable
      fun_prop
    refine (memLp_two_iff_integrable_sq hmeas).2 ?_
    have h1 : Integrable (fun ξ : ℂ => ((1 + ‖ξ‖ ^ 2 : ℝ)) ^ (-(4:ℝ)/2)) volume :=
      integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
        (by rw [Complex.finrank_real_complex]; norm_num)
    refine h1.congr ?_
    filter_upwards with ξ
    exact rpow_neg_half4 _
  -- Transfer square-integrability to the complex-valued reciprocal weight, which is the factor
  -- that multiplies `V` in `ℂ`.
  have hφc : MemLp (fun ξ : ℂ => ((((1 + ‖ξ‖ ^ 2 : ℝ)) : ℂ))⁻¹) 2 volume := by
    refine hφ.congr_norm ?_ ?_
    · apply Measurable.aestronglyMeasurable; fun_prop
    · filter_upwards with ξ
      have hb : (0:ℝ) < 1 + ‖ξ‖^2 := by positivity
      have h2 : ‖((((1 + ‖ξ‖ ^ 2 : ℝ)) : ℂ)⁻¹)‖ = ((1 + ‖ξ‖ ^ 2 : ℝ))⁻¹ := by
        rw [norm_inv,
          show ‖(((1 + ‖ξ‖ ^ 2 : ℝ)) : ℂ)‖ = |(1 + ‖ξ‖ ^ 2 : ℝ)|
            from RCLike.norm_ofReal _, abs_of_pos hb]
      rw [h2, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- The `N = 1` moment `(1+‖ξ‖²)·V` lies in `L²`.
  have hg : MemLp (fun ξ : ℂ => (((1 + ‖ξ‖ ^ 2 : ℝ)) : ℂ) * V ξ) 2 volume := by
    have h := hmom 1
    simpa using h
  -- Hölder with the triple `2, 2, 1`: the product of two `L²` functions is `L¹`.
  have hprod : MemLp (fun ξ : ℂ =>
      ((((1 + ‖ξ‖ ^ 2 : ℝ)) : ℂ))⁻¹ * ((((1 + ‖ξ‖ ^ 2 : ℝ)) : ℂ) * V ξ)) 1 volume :=
    hφc.mul hg
  -- The product equals `V` since `(1+‖ξ‖²)` never vanishes.
  refine hprod.ae_eq ?_
  filter_upwards with ξ
  have hb : ((1:ℝ) + ‖ξ‖^2) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hb), one_mul]

end Work.Beltrami
