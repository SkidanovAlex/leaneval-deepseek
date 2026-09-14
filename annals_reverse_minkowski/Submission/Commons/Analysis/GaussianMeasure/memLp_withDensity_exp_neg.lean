import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.integrable_mul_exp_neg_stronglyConvex

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Real
open scoped ENNReal

/-- A continuous function of at most polynomial growth lies in `L²(e^{-f} dx)` when
`f - π‖·‖²` is convex. -/
theorem memLp_withDensity_exp_neg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f Φ : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2))
    (hΦc : Continuous Φ)
    (hΦ : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x : E, |Φ x| ≤ C * (1 + ‖x‖) ^ N) :
    MemLp Φ 2 (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(f x))))) := by
  obtain ⟨C, hC, N, hΦbound⟩ := hΦ
  set w : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-(f x))) with hwdef
  have hf_cont : Continuous f := hf.continuous
  have hw_meas : Measurable w :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hf_cont.neg).measurable
  have hw_lt_top : ∀ᵐ x ∂(volume : Measure E), w x < ∞ :=
    ae_of_all _ (fun x => ENNReal.ofReal_lt_top)
  have hΦ_asm : AEStronglyMeasurable Φ (volume.withDensity w) :=
    hΦc.measurable.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hΦ_asm]
  rw [integrable_withDensity_iff_integrable_smul' hw_meas hw_lt_top]
  have hfun : (fun x : E => (w x).toReal • Φ x ^ 2)
      = fun x : E => Φ x ^ 2 * Real.exp (-(f x)) := by
    funext x
    simp only [hwdef]
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    ring
  rw [hfun]
  refine Commons.Analysis.GaussianMeasure.integrable_mul_exp_neg_stronglyConvex f
    (fun x => Φ x ^ 2) hf hconv (hΦc.pow 2) (C ^ 2) (sq_nonneg C) (2 * N) (fun x => ?_)
  have h1 : |Φ x ^ 2| = |Φ x| ^ 2 := by rw [pow_two, abs_mul, pow_two]
  rw [h1]
  have h2 : |Φ x| ^ 2 ≤ (C * (1 + ‖x‖) ^ N) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hΦbound x) 2
  refine le_trans h2 ?_
  rw [mul_pow, ← pow_mul, Nat.mul_comm]

end Commons.Analysis.GaussianMeasure
