import Mathlib
import Submission.Work.HP.Defs

/-!
# The mean of `‖x‖ ^ 2` over the unit ball

For a finite-dimensional real inner product space `V` of dimension `n = finrank ℝ V`, the integral
of `‖x‖ ^ 2` against the Lebesgue (Haar) measure over the closed unit ball equals
`n / (n + 2)` times the volume of the ball.  Equivalently, the uniform distribution on the unit
ball has second moment `n / (n + 2)`.

The mathematically substantive input is Mathlib's polar-coordinate formula
`MeasureTheory.integral_fun_norm_addHaar`: for a radial integrand `f ‖·‖` one has
`∫ x, f ‖x‖ ∂μ = finrank ℝ V • μ.real (ball 0 1) • ∫ y in Ioi 0, y ^ (finrank ℝ V - 1) • f y`.
Taking `f` to be the indicator of `(0, 1]` times `y ↦ y ^ 2` reduces the claim to the elementary
integral `∫_0^1 y ^ (n + 1) dy = 1 / (n + 2)`.  The measure of the ball and of the closed ball
coincide for a Haar measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace Work.HP

/-- The elementary radial integral appearing in the polar-coordinate computation of the second
moment of the Euclidean norm over the unit ball in dimension `n ≥ 1`:
`∫_0^∞ y ^ (n - 1) • (1_{y ≤ 1} y ^ 2) dy = 1 / (n + 2)`. -/
lemma ioi_indicator_pow_integral (n : ℕ) (hn : 1 ≤ n) :
    (∫ y in Set.Ioi (0 : ℝ), y ^ (n - 1) • (Set.Iic 1).indicator (fun y : ℝ => y ^ 2) y)
      = 1 / ((n : ℝ) + 2) := by
  -- On `(0, ∞)` the product `y ^ (n - 1) * (1_{y ≤ 1} y ^ 2)` is the indicator of `(0, 1]`
  -- times `y ^ (n + 1)`.
  have hpow : (∫ y in Set.Ioi (0 : ℝ),
        y ^ (n - 1) • (Set.Iic 1).indicator (fun y : ℝ => y ^ 2) y)
      = ∫ y in Set.Ioi (0 : ℝ), (Set.Iic 1).indicator (fun y : ℝ => y ^ (n + 1)) y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    simp only [Set.indicator_apply]
    by_cases hy1 : y ∈ Set.Iic (1 : ℝ)
    · rw [ite_eq_left hy1, ite_eq_left hy1, smul_eq_mul, ← pow_add]
      congr 1
      omega
    · rw [ite_eq_right hy1, ite_eq_right hy1, smul_eq_mul, mul_zero]
  rw [hpow, MeasureTheory.setIntegral_indicator measurableSet_Iic]
  rw [show Set.Ioi (0 : ℝ) ∩ Set.Iic (1 : ℝ) = Set.Ioc 0 1 by
        ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iic, Set.mem_Ioc]]
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [integral_pow (n + 1)]
  rw [show (1 : ℝ) ^ (n + 1 + 1) = 1 by simp]
  rw [show (0 : ℝ) ^ (n + 1 + 1) = 0 by exact zero_pow (by omega)]
  rw [sub_zero, one_div]
  push_cast
  ring

theorem BallNormSqIntegral {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] :
    ∫ x in Metric.closedBall (0 : V) 1, ‖x‖ ^ 2 ∂MeasureTheory.volume =
      ((Module.finrank ℝ V : ℝ) / ((Module.finrank ℝ V : ℝ) + 2)) *
        (MeasureTheory.volume (Metric.closedBall 0 1 : Set V)).toReal := by
  -- `V` is nontrivial, hence of positive dimension, so `finrank ℝ V - 1 + 2 = finrank ℝ V + 1`.
  have hn1 : 1 ≤ Module.finrank ℝ V := Module.finrank_pos
  -- The integrand is radial: the indicator of the unit ball is the indicator of `(0, 1]` composed
  -- with `‖·‖`.
  have hfun : (Metric.closedBall (0 : V) 1).indicator (fun x => ‖x‖ ^ 2)
      = fun x => (Set.Iic (1 : ℝ)).indicator (fun r : ℝ => r ^ 2) ‖x‖ := by
    funext x
    by_cases hx : x ∈ Metric.closedBall (0 : V) 1
    · have hxn : ‖x‖ ∈ Set.Iic (1 : ℝ) := by
        rw [Set.mem_Iic]
        rwa [Metric.mem_closedBall, dist_zero_right] at hx
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxn]
    · have hxn : ‖x‖ ∉ Set.Iic (1 : ℝ) := by
        rw [Set.mem_Iic]
        rwa [Metric.mem_closedBall, dist_zero_right] at hx
      simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxn]
  rw [← MeasureTheory.integral_indicator measurableSet_closedBall, hfun]
  -- Polar-coordinate formula reduces the whole-space integral of a radial function to an integral
  -- over `(0, ∞)`, with a factor `finrank ℝ V • volume.real (ball 0 1)`.
  rw [MeasureTheory.integral_fun_norm_addHaar volume
        (fun r : ℝ => (Set.Iic (1 : ℝ)).indicator (fun r => r ^ 2) r)]
  rw [ioi_indicator_pow_integral (Module.finrank ℝ V) hn1]
  -- The Haar measure of the open and closed unit balls agree.
  have hvol : volume.real (Metric.ball (0 : V) 1)
      = (volume (Metric.closedBall (0 : V) 1)).toReal := by
    rw [MeasureTheory.Measure.real_def,
        ← MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : V) 1]
  rw [hvol]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

end Work.HP
