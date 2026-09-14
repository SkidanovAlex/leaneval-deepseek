import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Commons.Analysis.GaussianMeasure.convex_sub_quadratic_lower_bound
import Submission.Commons.Analysis.Calculus.pow_mul_exp_neg_sq_bounded

namespace Commons.Analysis.Elliptic

open MeasureTheory
open scoped ENNReal

/-- For `a > 0` and `N : ℕ`, the function `t ↦ (1 + t) ^ N * exp (-a * t ^ 2)` is bounded above
on `[0, ∞)`. -/
theorem exists_bound_one_add_pow_mul_exp_neg_sq (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ N * Real.exp (-a * t ^ 2) ≤ M := by
  obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.Calculus.pow_mul_exp_neg_sq_bounded a ha N
  refine ⟨(2 : ℝ) ^ N * C, by positivity, fun t ht => ?_⟩
  have hle : (1 + t) ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg t, ht, sq_nonneg (t - 1)]
  have hpow : (1 + t) ^ N ≤ (2 * (1 + t ^ 2)) ^ N :=
    pow_le_pow_left₀ (by positivity) hle N
  calc (1 + t) ^ N * Real.exp (-a * t ^ 2)
      ≤ (2 * (1 + t ^ 2)) ^ N * Real.exp (-a * t ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = (2 : ℝ) ^ N * ((1 + t ^ 2) ^ N * Real.exp (-a * t ^ 2)) := by rw [mul_pow]; ring
    _ ≤ (2 : ℝ) ^ N * C := mul_le_mul_of_nonneg_left (hC t) (by positivity)


/-- The norm of a real number viewed as a complex number. -/
private theorem norm_complex_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = ‖r‖ := by
  have h1 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  calc ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h1]
    _ = |r| := Real.sqrt_sq_eq_abs r
    _ = ‖r‖ := (Real.norm_eq_abs r).symm

theorem memLp_psi_and_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E, |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.withDensity (fun x : E => ENNReal.ofReal (Real.exp (-(f x)))))) : MeasureTheory.MemLp (fun x : E => ((g x * Real.exp (-(f x)) : ℝ) : ℂ)) 2 MeasureTheory.volume ∧ MeasureTheory.MemLp (fun x : E => ((g x * Real.exp (-(f x)) : ℝ) : ℂ) * ((‖fderiv ℝ f x‖ : ℝ) : ℂ)) 2 MeasureTheory.volume := by
  have hf_cont : Continuous f := hf.continuous
  -- quadratic lower bound coming from convexity
  obtain ⟨c, hc⟩ :=
    Commons.Analysis.GaussianMeasure.convex_sub_quadratic_lower_bound f
      ((hf.differentiable (by norm_num)) 0) hconv
  have hexp1 : ∀ x : E,
      Real.exp (-(f x)) ≤ Real.exp c * Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2) := by
    intro x
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hc x
    nlinarith
  have hexp2 : ∀ x : E, Real.exp (-(f x)) ≤ Real.exp c := by
    intro x
    refine le_trans (hexp1 x) (mul_le_of_le_one_right (Real.exp_nonneg c) ?_)
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg ‖x‖, Real.pi_pos]
  -- polynomial bound on the gradient
  obtain ⟨C0, hC0, N0, hN0⟩ := hgf
  have hnorm_fderiv : ∀ x : E, ‖fderiv ℝ f x‖ ≤ C0 * (1 + ‖x‖) ^ N0 := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC0 (pow_nonneg (by positivity) N0)) ?_
    intro v
    rw [Real.norm_eq_abs]
    have := hN0 x v
    simpa only [mul_assoc] using this
  -- bound on `exp(-f) * ‖∇f‖²`
  obtain ⟨M2, _hM2pos, hM2⟩ :=
    exists_bound_one_add_pow_mul_exp_neg_sq (2 * N0) (a := Real.pi / 2) (by positivity)
  have hgrad_bound : ∀ x : E,
      Real.exp (-(f x)) * ‖fderiv ℝ f x‖ ^ 2 ≤ Real.exp c * C0 ^ 2 * M2 := by
    intro x
    have h2 : ‖fderiv ℝ f x‖ ^ 2 ≤ (C0 * (1 + ‖x‖) ^ N0) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm_fderiv x) 2
    have h3 : (C0 * (1 + ‖x‖) ^ N0) ^ 2 = C0 ^ 2 * (1 + ‖x‖) ^ (2 * N0) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm]
    have hb : ‖fderiv ℝ f x‖ ^ 2 ≤ C0 ^ 2 * (1 + ‖x‖) ^ (2 * N0) := by
      rw [← h3]; exact h2
    have h4 := hM2 ‖x‖ (norm_nonneg x)
    calc Real.exp (-(f x)) * ‖fderiv ℝ f x‖ ^ 2
        ≤ (Real.exp c * Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) *
            (C0 ^ 2 * (1 + ‖x‖) ^ (2 * N0)) :=
          mul_le_mul (hexp1 x) hb (by positivity) (by positivity)
      _ = Real.exp c * C0 ^ 2 *
            ((1 + ‖x‖) ^ (2 * N0) * Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) := by ring
      _ ≤ Real.exp c * C0 ^ 2 * M2 := mul_le_mul_of_nonneg_left h4 (by positivity)
  -- set up the weighted measure
  set W : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-(f x))) with hW
  have hW_measble : Measurable W := by
    rw [hW]
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp hf_cont.neg.measurable)
  have hW_meas : AEMeasurable W volume := hW_measble.aemeasurable
  have hW_ne : ∀ᵐ x ∂(volume : Measure E), W x ≠ 0 := by
    filter_upwards with x
    rw [hW]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hW_lt : ∀ᵐ x ∂(volume : Measure E), W x < ∞ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have hac : (volume : Measure E) ≪ volume.withDensity W :=
    withDensity_absolutelyContinuous' hW_meas hW_ne
  have hgm : MemLp g 2 (volume.withDensity W) := by rw [hW]; exact hg
  have hg_asm_vol : AEStronglyMeasurable g volume := hgm.1.mono_ac hac
  -- `Integrable` of `g² e^{-f}` with respect to Lebesgue measure
  have hgi : Integrable (fun x : E => g x ^ 2) (volume.withDensity W) :=
    (memLp_two_iff_integrable_sq hgm.1).mp hgm
  have hgi' : Integrable (fun x : E => (W x).toReal • g x ^ 2) volume :=
    (integrable_withDensity_iff_integrable_smul' hW_measble hW_lt).mp hgi
  have hg1 : Integrable (fun x : E => g x ^ 2 * Real.exp (-(f x))) volume := by
    have hfun : (fun x : E => (W x).toReal • g x ^ 2)
        = fun x : E => g x ^ 2 * Real.exp (-(f x)) := by
      funext x
      rw [hW]
      simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
      ring
    rwa [hfun] at hgi'
  -- measurability of the two real-valued test functions
  have hA1 : AEStronglyMeasurable (fun x : E => g x * Real.exp (-(f x))) volume :=
    hg_asm_vol.mul ((Real.continuous_exp.comp hf_cont.neg).aestronglyMeasurable)
  have hfd_cont : Continuous (fun x : E => fderiv ℝ f x) :=
    hf.continuous_fderiv (by norm_num)
  have hA2 : AEStronglyMeasurable
      (fun x : E => (g x * Real.exp (-(f x))) * ‖fderiv ℝ f x‖) volume :=
    hA1.mul hfd_cont.norm.aestronglyMeasurable
  -- first conclusion
  have hint1 : Integrable (fun x : E => (g x * Real.exp (-(f x))) ^ 2) volume := by
    refine (hg1.const_mul (Real.exp c)).mono' (hA1.pow 2) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hkey : Real.exp (-(f x)) * Real.exp (-(f x)) ≤ Real.exp c * Real.exp (-(f x)) :=
      mul_le_mul_of_nonneg_right (hexp2 x) (Real.exp_nonneg _)
    calc (g x * Real.exp (-(f x))) ^ 2
        = g x ^ 2 * (Real.exp (-(f x)) * Real.exp (-(f x))) := by ring
      _ ≤ g x ^ 2 * (Real.exp c * Real.exp (-(f x))) :=
          mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
      _ = Real.exp c * (g x ^ 2 * Real.exp (-(f x))) := by ring
  have hmem1r : MemLp (fun x : E => g x * Real.exp (-(f x))) 2 volume :=
    (memLp_two_iff_integrable_sq hA1).mpr hint1
  have hmem1 : MemLp (fun x : E => ((g x * Real.exp (-(f x)) : ℝ) : ℂ)) 2 volume := by
    refine hmem1r.of_le ?_ ?_
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hA1
    · filter_upwards with x
      rw [norm_complex_ofReal]
  -- second conclusion
  have hint2 : Integrable
      (fun x : E => ((g x * Real.exp (-(f x))) * ‖fderiv ℝ f x‖) ^ 2) volume := by
    refine (hg1.const_mul (Real.exp c * C0 ^ 2 * M2)).mono' (hA2.pow 2) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc ((g x * Real.exp (-(f x))) * ‖fderiv ℝ f x‖) ^ 2
        = (g x ^ 2 * Real.exp (-(f x))) * (Real.exp (-(f x)) * ‖fderiv ℝ f x‖ ^ 2) := by ring
      _ ≤ (g x ^ 2 * Real.exp (-(f x))) * (Real.exp c * C0 ^ 2 * M2) :=
          mul_le_mul_of_nonneg_left (hgrad_bound x) (by positivity)
      _ = Real.exp c * C0 ^ 2 * M2 * (g x ^ 2 * Real.exp (-(f x))) := by ring
  have hmem2r : MemLp (fun x : E => (g x * Real.exp (-(f x))) * ‖fderiv ℝ f x‖) 2 volume :=
    (memLp_two_iff_integrable_sq hA2).mpr hint2
  have hA1c : AEStronglyMeasurable
      (fun x : E => ((g x * Real.exp (-(f x)) : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hA1
  have hA2c : AEStronglyMeasurable
      (fun x : E => ((g x * Real.exp (-(f x)) : ℝ) : ℂ) * ((‖fderiv ℝ f x‖ : ℝ) : ℂ)) volume :=
    hA1c.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
      hfd_cont.norm.aestronglyMeasurable)
  have hmem2 : MemLp
      (fun x : E => ((g x * Real.exp (-(f x)) : ℝ) : ℂ) * ((‖fderiv ℝ f x‖ : ℝ) : ℂ)) 2 volume := by
    refine hmem2r.of_le hA2c ?_
    filter_upwards with x
    rw [Complex.norm_mul, norm_complex_ofReal, norm_complex_ofReal]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
    exact le_refl _
  exact ⟨hmem1, hmem2⟩

end Commons.Analysis.Elliptic