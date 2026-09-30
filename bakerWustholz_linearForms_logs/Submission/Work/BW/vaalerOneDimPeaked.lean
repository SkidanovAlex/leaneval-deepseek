import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vaaler's one-dimensional peaked-function bound

For `a ≥ 0` we show that the Gaussian bump `x ↦ exp(-π x²)` has integral over `[-a, a]`
at most the measure of `[-a, a] ∩ [-1/2, 1/2]`, i.e. at most the integral of the
indicator of the unit interval `[-1/2, 1/2]` over `[-a, a]`.

Both sides reduce to `2 * min a (1/2)`:

* the right hand side is exactly the measure `|[-a,a] ∩ [-1/2,1/2]| = 2 * min a (1/2)`;
* the left hand side is bounded by `min (2a) 1 = 2 * min a (1/2)`, since `exp (-π x²) ≤ 1`
  gives the bound `2a`, while monotonicity together with the Gaussian integral
  `∫ x, exp (-π x²) = 1` gives the bound `1`.
-/

namespace Work.BW

open MeasureTheory

/-- The full Gaussian integral in the normalisation used by Vaaler:
`∫ x : ℝ, exp (-π x²) = 1`. -/
private lemma integral_exp_neg_pi_sq :
    ∫ x : ℝ, Real.exp (-(Real.pi * x^2)) = 1 := by
  have h := integral_gaussian Real.pi
  rw [div_self Real.pi_ne_zero, Real.sqrt_one] at h
  rw [← h]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [neg_mul]

/-- The right hand side of the inequality: the integral of the indicator of `[-1/2, 1/2]`
over `[-a, a]` is the measure of the intersection, equal to `2 * min a (1/2)`. -/
private lemma indicatorIcc_integral (a : ℝ) (ha : 0 ≤ a) :
    ∫ x in Set.Icc (-a) a, (Set.Icc (-(1/2:ℝ)) (1/2)).indicator (fun _ => (1:ℝ)) x
      = 2 * min a (1/2) := by
  rw [MeasureTheory.setIntegral_indicator measurableSet_Icc]
  rw [MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, mul_one, MeasureTheory.Measure.real]
  rw [Set.Icc_inter_Icc, max_neg_neg]
  rw [Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by have := le_min ha (show (0:ℝ) ≤ 1/2 by norm_num); linarith)]
  ring

/-- The left hand side is at most `2 * min a (1/2)`. -/
private lemma exp_integral_le (a : ℝ) (ha : 0 ≤ a) :
    ∫ x in Set.Icc (-a) a, Real.exp (-(Real.pi * x^2)) ≤ 2 * min a (1/2) := by
  have he : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-(Real.pi * x^2)))
      (Set.Icc (-a) a) :=
    Continuous.integrableOn_Icc (by fun_prop)
  have hg : MeasureTheory.IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc (-a) a) :=
    Continuous.integrableOn_Icc continuous_const
  have h2a : ∫ x in Set.Icc (-a) a, Real.exp (-(Real.pi * x^2)) ≤ 2 * a := by
    have hmono : ∫ x in Set.Icc (-a) a, Real.exp (-(Real.pi * x^2))
        ≤ ∫ x in Set.Icc (-a) a, (1:ℝ) :=
      MeasureTheory.setIntegral_mono_on he hg measurableSet_Icc
        (fun x _ => by rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, sq_nonneg x])
    refine hmono.trans (le_of_eq ?_)
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one, MeasureTheory.Measure.real, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  have h1 : ∫ x in Set.Icc (-a) a, Real.exp (-(Real.pi * x^2)) ≤ 1 := by
    rw [← integral_exp_neg_pi_sq]
    apply MeasureTheory.setIntegral_le_integral
    · simpa only [neg_mul] using (integrable_exp_neg_mul_sq Real.pi_pos)
    · filter_upwards with x
      exact Real.exp_nonneg _
  have key : min (2*a) 1 = 2 * min a (1/2) := by
    rcases lt_or_ge a (1/2) with h | h
    · have h2' : 2*a ≤ 1 := by linarith
      rw [min_eq_left h2', min_eq_left (le_of_lt h)]
    · have h2' : 1 ≤ 2*a := by linarith
      rw [min_eq_right h2', min_eq_right h]
      norm_num
  exact le_trans (le_min h2a h1) (le_of_eq key)

theorem vaalerOneDimPeaked (a : ℝ) (ha : 0 ≤ a) :
    ∫ x in Set.Icc (-a) a, Real.exp (-(Real.pi * x^2))
      ≤ ∫ x in Set.Icc (-a) a, (Set.Icc (-(1/2:ℝ)) (1/2)).indicator (fun _ => (1:ℝ)) x := by
  rw [indicatorIcc_integral a ha]
  exact exp_integral_le a ha

end Work.BW
