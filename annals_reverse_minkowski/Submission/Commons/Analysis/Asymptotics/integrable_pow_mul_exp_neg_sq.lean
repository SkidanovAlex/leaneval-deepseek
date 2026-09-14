import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace Commons.Analysis.Asymptotics

open MeasureTheory Real Filter
open scoped Real Topology

/-- Gaussian integrability in a finite-dimensional real inner product space:
`v ↦ exp (-d * ‖v‖^2)` is integrable for `d > 0`. -/
private lemma integrable_exp_neg_mul_sq_norm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {d : ℝ} (hd : 0 < d) :
    Integrable (fun v : V => Real.exp (-d * ‖v‖ ^ 2)) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V)
    (show 0 < ((d : ℂ)).re by simpa using hd) (0 : ℂ) (0 : V)
  have hre := h.re
  convert hre using 1
  ext v
  simp only [zero_mul, add_zero]
  have hh : -(d : ℂ) * ↑‖v‖ ^ 2 = ↑(-d * ‖v‖ ^ 2) := by push_cast; ring_nf
  rw [hh, ← Complex.ofReal_exp]
  exact Complex.ofReal_re _

/-- A polynomial is dominated by an exponential of a positive multiple of the square. -/
private lemma one_add_pow_le_exp_mul_exp_sq (δ : ℝ) (hδ : 0 < δ) (N : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    (1 + t) ^ N ≤ Real.exp ((N : ℝ) ^ 2 / (4 * δ)) * Real.exp (δ * t ^ 2) := by
  have h1 : (1 + t) ^ N ≤ (Real.exp t) ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    linarith [Real.add_one_le_exp t]
  have h3 : (N : ℝ) * t ≤ (N : ℝ) ^ 2 / (4 * δ) + δ * t ^ 2 := by
    rw [← mul_le_mul_iff_right₀ (show (0 : ℝ) < 4 * δ by linarith)]
    have heq : 4 * δ * ((N : ℝ) ^ 2 / (4 * δ) + δ * t ^ 2)
        = (N : ℝ) ^ 2 + 4 * δ ^ 2 * t ^ 2 := by
      field_simp
    rw [heq]
    nlinarith [sq_nonneg ((N : ℝ) - 2 * δ * t)]
  calc (1 + t) ^ N ≤ (Real.exp t) ^ N := h1
    _ = Real.exp ((N : ℝ) * t) := (Real.exp_nat_mul t N).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * δ) + δ * t ^ 2) := Real.exp_le_exp.mpr h3
    _ = Real.exp ((N : ℝ) ^ 2 / (4 * δ)) * Real.exp (δ * t ^ 2) := Real.exp_add _ _

/-- The Gaussian-type function `(1 + ‖v‖)^N * exp (-a * ‖v‖^2)` is integrable on any
finite-dimensional real inner product space, for `a > 0`. -/
theorem integrable_pow_mul_exp_neg_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (a : ℝ) (ha : 0 < a) (N : ℕ) :
    Integrable (fun v : V => (1 + ‖v‖) ^ N * Real.exp (-a * ‖v‖ ^ 2)) volume := by
  have hδ : (0 : ℝ) < a / 2 := by linarith
  have hg : Integrable
      (fun v : V => Real.exp ((N : ℝ) ^ 2 / (4 * (a / 2))) * Real.exp (-(a / 2) * ‖v‖ ^ 2))
      volume := (integrable_exp_neg_mul_sq_norm hδ).const_mul _
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Continuous
      (fun v : V => (1 + ‖v‖) ^ N * Real.exp (-a * ‖v‖ ^ 2))).aestronglyMeasurable
  · filter_upwards with v
    rw [Real.norm_of_nonneg (by positivity)]
    have hb := one_add_pow_le_exp_mul_exp_sq (a / 2) hδ N (norm_nonneg v)
    calc (1 + ‖v‖) ^ N * Real.exp (-a * ‖v‖ ^ 2)
        ≤ (Real.exp ((N : ℝ) ^ 2 / (4 * (a / 2))) * Real.exp ((a / 2) * ‖v‖ ^ 2))
            * Real.exp (-a * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = Real.exp ((N : ℝ) ^ 2 / (4 * (a / 2)))
            * (Real.exp ((a / 2) * ‖v‖ ^ 2) * Real.exp (-a * ‖v‖ ^ 2)) := by ring
      _ = Real.exp ((N : ℝ) ^ 2 / (4 * (a / 2))) * Real.exp (-(a / 2) * ‖v‖ ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf

end Commons.Analysis.Asymptotics