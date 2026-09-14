import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Set

theorem one_dim_tail_ten_le_sixth :
    (∫ x in Set.Ioi (10 : ℝ), Real.exp (-Real.pi * x ^ 2)) ≤ 1 / 6 := by
  -- For x > 10 we have π x² ≥ x, hence exp(-π x²) ≤ exp(-x).
  have hle_fun : ∀ x ∈ Set.Ioi (10 : ℝ),
      Real.exp (-Real.pi * x ^ 2) ≤ Real.exp (-x) := by
    intro x hx
    refine (Real.exp_le_exp).2 ?_
    have hx10 : (10 : ℝ) < x := hx
    have hxpos : 0 < x := lt_trans (by norm_num) hx10
    have hx10le : (10 : ℝ) ≤ x := le_of_lt hx10
    have h30lt : (30 : ℝ) < Real.pi * 10 := by
      nlinarith [Real.pi_gt_three]
    have hπx_gt30 : (30 : ℝ) < Real.pi * x := by
      have hle : Real.pi * (10 : ℝ) ≤ Real.pi * x :=
        mul_le_mul_of_nonneg_left hx10le (Real.pi_pos.le)
      exact lt_of_lt_of_le h30lt hle
    have hπx1 : 0 ≤ Real.pi * x - 1 := by linarith
    have hfac : 0 ≤ x * (Real.pi * x - 1) :=
      mul_nonneg (le_of_lt hxpos) hπx1
    nlinarith
  -- Integrability of both functions on (10, ∞).
  have hf_int : IntegrableOn (fun x : ℝ => Real.exp (-Real.pi * x ^ 2))
      (Set.Ioi (10 : ℝ)) :=
    (integrable_exp_neg_mul_sq (b := Real.pi) Real.pi_pos).integrableOn
  have hg_int : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi (10 : ℝ)) :=
    integrableOn_exp_neg_Ioi (10 : ℝ)
  have hmain : (∫ x in Set.Ioi (10 : ℝ), Real.exp (-Real.pi * x ^ 2)) ≤
      ∫ x in Set.Ioi (10 : ℝ), Real.exp (-x) := by
    exact MeasureTheory.setIntegral_mono_on hf_int hg_int measurableSet_Ioi hle_fun
  -- ∫_{10}^{∞} exp(-x) dx = exp(-10)
  have hval : (∫ x in Set.Ioi (10 : ℝ), Real.exp (-x)) = Real.exp (-10) :=
    integral_exp_neg_Ioi (10 : ℝ)
  -- exp(-10) < 1/6, since 6 ≤ 11 ≤ exp 10.
  have h6exp : (6 : ℝ) * Real.exp (-10) ≤ 1 := by
    have h11 : (10 : ℝ) + 1 ≤ Real.exp 10 := Real.add_one_le_exp (10 : ℝ)
    have h6le10 : (6 : ℝ) ≤ Real.exp 10 := by nlinarith
    calc
      (6 : ℝ) * Real.exp (-10) ≤ Real.exp 10 * Real.exp (-10) :=
        mul_le_mul_of_nonneg_right h6le10 (Real.exp_pos (-10)).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  have hexp_le : Real.exp (-10) ≤ (1 : ℝ) / 6 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
    nlinarith [h6exp]
  linarith

end Commons.Analysis.GaussianMeasure