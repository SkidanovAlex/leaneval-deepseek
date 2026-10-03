import Mathlib

open MeasureTheory

namespace Work.Analysis.Fourier

/-- If a function `f` on `AddCircle 1` is the pointwise sum of the Fourier series with
coefficients `a`, and the coefficients are absolutely summable, then `a` is exactly the
sequence of Fourier coefficients of `f`. -/
theorem fourierCoeff_summable_series {a : ℤ → ℂ} (ha : Summable fun j => ‖a j‖)
    {f : AddCircle (1 : ℝ) → ℂ}
    (hf : ∀ ξ, HasSum (fun j => a j * fourier (T := 1) j ξ) (f ξ)) :
    fourierCoeff f = a := by
  ext n
  -- `f` agrees pointwise with the sum of the series.
  have hf_tsum : ∀ ξ, f ξ = ∑' j, a j * fourier (T := 1) j ξ :=
    fun ξ => (hf ξ).tsum_eq.symm
  -- The norm of the `j`-th summand is the constant `‖a j‖`.
  have hpt_norm : ∀ (j : ℤ) (t : AddCircle (1:ℝ)),
      ‖fourier (T := 1) (-n) t • (a j * fourier (T := 1) j t)‖ = ‖a j‖ := by
    intro j t
    rw [norm_smul, norm_mul, fourier_apply, Circle.norm_coe, one_mul]
    rw [fourier_apply, Circle.norm_coe, mul_one]
  -- Each summand is integrable (it is continuous and bounded on the compact circle).
  have hFint : ∀ j : ℤ, Integrable (fun t : AddCircle (1:ℝ) =>
      fourier (T := 1) (-n) t • (a j * fourier (T := 1) j t)) AddCircle.haarAddCircle := by
    intro j
    refine Integrable.of_bound ?_ (‖a j‖) ?_
    · simp only [smul_eq_mul]
      exact ((map_continuous (fourier (T := 1) (-n))).mul
        (continuous_const.mul (map_continuous (fourier (T := 1) j)))).aestronglyMeasurable
    · filter_upwards with t
      exact le_of_eq (hpt_norm j t)
  -- The integrals of the norms are exactly the norms `‖a j‖`.
  have hint : ∀ j : ℤ, (∫ t : AddCircle (1:ℝ),
      ‖fourier (T := 1) (-n) t • (a j * fourier (T := 1) j t)‖ ∂AddCircle.haarAddCircle) = ‖a j‖ := by
    intro j
    simp_rw [hpt_norm j]
    rw [integral_const, Measure.real, MeasureTheory.measure_univ, ENNReal.toReal_one, one_smul]
  -- Hence the family of `L¹` norms is summable, by hypothesis.
  have hFsum : Summable (fun j : ℤ => (∫ t : AddCircle (1:ℝ),
      ‖fourier (T := 1) (-n) t • (a j * fourier (T := 1) j t)‖ ∂AddCircle.haarAddCircle)) := by
    simpa only [hint] using ha
  -- Interchange the integral and the sum.
  have hmain := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hterm : ∀ j : ℤ, (∫ t : AddCircle (1:ℝ),
        fourier (T := 1) (-n) t • (a j * fourier (T := 1) j t) ∂AddCircle.haarAddCircle)
      = a j * fourierCoeff (fourier (T := 1) j) n := fun j =>
    fourierCoeff.const_mul (fourier (T := 1) j) (a j) n
  have hRHS : (∫ t : AddCircle (1:ℝ), ∑' j, fourier (T := 1) (-n) t • (a j * fourier (T := 1) j t)
        ∂AddCircle.haarAddCircle) = fourierCoeff f n := by
    rw [fourierCoeff]
    apply integral_congr_ae
    filter_upwards with t
    rw [show (∑' j, fourier (T := 1) (-n) t • (a j * fourier (T := 1) j t))
        = ∑' j, fourier (T := 1) (-n) t * (a j * fourier (T := 1) j t) by
      simp only [smul_eq_mul]]
    rw [tsum_mul_left, hf_tsum t]
    simp only [smul_eq_mul]
  simp only [hterm] at hmain
  rw [hRHS] at hmain
  -- The series has a single non-zero term, equal to `a n`.
  have huniq : HasSum (fun j => a j * fourierCoeff (fourier (T := 1) j) n) (a n) := by
    have h1 : (fun j => a j * fourierCoeff (fourier (T := 1) j) n)
        = fun j => if j = n then a n else 0 := by
      funext j
      rw [fourierCoeff_fourier]
      by_cases h : j = n
      · subst h
        rw [Pi.single_eq_same, if_pos rfl, mul_one]
      · rw [Pi.single_eq_of_ne (Ne.symm h) 1, if_neg h, mul_zero]
    rw [h1]
    exact hasSum_ite_eq n (a n)
  exact hmain.unique huniq

end Work.Analysis.Fourier
