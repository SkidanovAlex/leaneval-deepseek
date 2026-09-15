import Mathlib
import Submission.Commons.Analysis.Fourier.FT_strip_integral_eq
import Submission.Commons.Analysis.Fourier.LogvinenkoSereda.bandlimited_entire_extension_cube

open MeasureTheory FourierTransform
open scoped BigOperators ENNReal

namespace Commons.Analysis.Fourier

/-- The `L²`-Plancherel identity along a horizontal slice of the Fourier--Laplace transform,
in `lintegral` form: for `H` integrable and a.e. supported in the band cube
`{a | ∀ i, |a i| ≤ σ}` and every `y : Fin d → ℝ`,
`∫⁻_x ‖FT (x + i y)‖² = ∫⁻_ξ ‖H ξ‖² exp(-4π ∑ᵢ yᵢ ξᵢ)`.
Unlike the Bochner-integral form `FT_strip_integral_eq` this needs no sign hypothesis on `σ`
(the identity is between extended-nonnegative reals and both sides may be infinite). -/
theorem lintegral_FT_slice_eq {d : ℕ} {σ : ℝ}
    {H : EuclideanSpace ℝ (Fin d) → ℂ} (hH : MeasureTheory.Integrable H)
    (hsupp : ∀ᵐ a ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      a ∉ {a : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, |a i| ≤ σ} → H a = 0)
    (y : Fin d → ℝ) :
    ∫⁻ x : EuclideanSpace ℝ (Fin d), ENNReal.ofReal
        ‖Commons.Analysis.Fourier.LogvinenkoSereda.FT d H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2
      = ∫⁻ a : EuclideanSpace ℝ (Fin d),
          ENNReal.ofReal (‖H a‖ ^ 2 * Real.exp (-(4 * Real.pi) * ∑ i : Fin d, y i * a i)) := by
  classical
  let C : ℝ := Real.exp (2 * Real.pi * max σ 0 * ∑ i : Fin d, |y i|)
  let G : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun a => H a * (Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i) : ℂ)
  have hsum_cont : Continuous (fun a : EuclideanSpace ℝ (Fin d) => ∑ i : Fin d, y i * a i) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (EuclideanSpace.proj i).continuous
  -- Integrability of the weight-twisted function `G`.
  have hGint : Integrable G := by
    refine (hH.norm.const_mul C).mono' ?_ ?_
    · simp only [G]
      exact hH.aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp (continuous_const.mul hsum_cont))).aestronglyMeasurable
    · filter_upwards [hsupp] with a ha
      by_cases hmem : a ∈ LogvinenkoSereda.bandCube d σ
      · have hmem' : a ∈ {a : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, |a i| ≤ σ} := hmem
        have hsumbound : |∑ i : Fin d, y i * a i| ≤ max σ 0 * ∑ i : Fin d, |y i| := by
          calc |∑ i : Fin d, y i * a i| ≤ ∑ i : Fin d, |y i * a i| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = ∑ i : Fin d, |y i| * |a i| := by simp [abs_mul]
            _ ≤ ∑ i : Fin d, |y i| * max σ 0 := by
                  refine Finset.sum_le_sum fun i _ => ?_
                  exact mul_le_mul_of_nonneg_left
                    ((hmem i).trans (le_max_left σ 0)) (abs_nonneg _)
            _ = max σ 0 * ∑ i : Fin d, |y i| := by rw [← Finset.sum_mul, mul_comm]
        have hexp : Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i) ≤ C := by
          simp only [C]
          apply Real.exp_le_exp.mpr
          have h1 : -(2 * Real.pi) * ∑ i : Fin d, y i * a i
              ≤ 2 * Real.pi * |∑ i : Fin d, y i * a i| := by
            have := neg_le_abs (∑ i : Fin d, y i * a i)
            nlinarith [abs_nonneg (∑ i : Fin d, y i * a i), Real.pi_pos]
          have h2 : 2 * Real.pi * |∑ i : Fin d, y i * a i|
              ≤ 2 * Real.pi * (max σ 0 * ∑ i : Fin d, |y i|) :=
            mul_le_mul_of_nonneg_left hsumbound (by positivity)
          have h3 : 2 * Real.pi * (max σ 0 * ∑ i : Fin d, |y i|)
              = 2 * Real.pi * max σ 0 * ∑ i : Fin d, |y i| := by ring
          linarith [h2.trans_eq h3]
        dsimp only [G]
        rw [norm_mul, norm_ofReal_exp]
        calc ‖H a‖ * Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i)
            ≤ ‖H a‖ * C := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
          _ = C * ‖H a‖ := mul_comm _ _
      · have h0 : H a = 0 := ha hmem
        simp [G, h0]
  -- Pointwise identification of the slice of the Fourier--Laplace transform.
  have hFT : ∀ x : EuclideanSpace ℝ (Fin d),
      LogvinenkoSereda.FT d H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = 𝓕⁻ G x := by
    intro x
    have hy : ((EuclideanSpace.equiv (Fin d) ℝ).symm y).ofLp = y := rfl
    have h := FT_apply_add_I_mul_eq H x ((EuclideanSpace.equiv (Fin d) ℝ).symm y)
    rw [hy] at h
    simpa only [LogvinenkoSereda.FT, LogvinenkoSereda.phase, G] using h
  calc ∫⁻ x : EuclideanSpace ℝ (Fin d), ENNReal.ofReal
        ‖LogvinenkoSereda.FT d H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2
      = ∫⁻ x : EuclideanSpace ℝ (Fin d), ‖𝓕⁻ G x‖ₑ ^ 2 := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only []
        rw [hFT x, ← ofReal_norm, ENNReal.rpow_ofNat]
    _ = ∫⁻ a : EuclideanSpace ℝ (Fin d), ‖G a‖ₑ ^ 2 :=
        lintegral_enorm_sq_fourierInv_eq_of_integrable hGint
    _ = ∫⁻ a : EuclideanSpace ℝ (Fin d),
          ENNReal.ofReal (‖H a‖ ^ 2 * Real.exp (-(4 * Real.pi) * ∑ i : Fin d, y i * a i)) := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        show ‖G a‖ₑ ^ (2:ℝ) = ENNReal.ofReal
          (‖H a‖ ^ 2 * Real.exp (-(4 * Real.pi) * ∑ i : Fin d, y i * a i))
        have hn : ‖G a‖ = ‖H a‖ * Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i) := by
          dsimp only [G]
          rw [norm_mul, norm_ofReal_exp]
        have hr : Real.exp (-(4 * Real.pi) * ∑ i : Fin d, y i * a i)
            = (Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i)) ^ 2 := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        have hX : ‖H a‖ ^ 2 * Real.exp (-(4 * Real.pi) * ∑ i : Fin d, y i * a i) = ‖G a‖ ^ 2 := by
          rw [hn, mul_pow, hr]
        rw [hX, ENNReal.ofReal_pow (norm_nonneg (G a)), ofReal_norm, ENNReal.rpow_ofNat]

end Commons.Analysis.Fourier
