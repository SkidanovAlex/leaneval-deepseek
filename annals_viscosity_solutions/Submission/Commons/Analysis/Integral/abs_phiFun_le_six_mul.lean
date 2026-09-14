import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Integral

/-- Positivity of the base `1 + v² + 2 v cos θ` for `0 < v ≤ 1/2`. -/
lemma one_add_sq_add_two_mul_cos_pos {v θ : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 2) :
    0 < 1 + v ^ 2 + 2 * v * Real.cos θ := by
  have hcos : 0 ≤ 1 + Real.cos θ := by linarith [Real.neg_one_le_cos θ]
  have h1v : 0 < 1 - v := by linarith
  have hprod : 0 ≤ 2 * v * (1 + Real.cos θ) := mul_nonneg (by linarith) hcos
  have heq : 1 + v ^ 2 + 2 * v * Real.cos θ = (1 - v) ^ 2 + 2 * v * (1 + Real.cos θ) := by
    ring
  rw [heq]
  have : 0 < (1 - v) ^ 2 := sq_pos_of_ne_zero (ne_of_gt h1v)
  linarith

/-- Pointwise bound: for `0 < v ≤ 1/2` and every `θ`,
`|(1 + v² + 2 v cos θ)^{-1/2} - 1| ≤ 6 v`. -/
lemma abs_rpow_neg_half_sub_one_le {v θ : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 2) :
    |(1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2) - 1| ≤ 6 * v := by
  set u : ℝ := 1 + v ^ 2 + 2 * v * Real.cos θ with hu
  have hu_pos : 0 < u := one_add_sq_add_two_mul_cos_pos hv0 hv
  have hcos : 0 ≤ 1 + Real.cos θ := by linarith [Real.neg_one_le_cos θ]
  have h1v : 0 < 1 - v := by linarith
  have hprod : 0 ≤ 2 * v * (1 + Real.cos θ) := mul_nonneg (by linarith) hcos
  have hu_eq : u = (1 - v) ^ 2 + 2 * v * (1 + Real.cos θ) := by rw [hu]; ring
  have hs_ge : 1 - v ≤ Real.sqrt u := by
    rw [← Real.sqrt_sq (le_of_lt h1v)]
    exact Real.sqrt_le_sqrt (by rw [hu_eq]; linarith)
  have hs_pos : 0 < Real.sqrt u := lt_of_lt_of_le h1v hs_ge
  have hrpow : u ^ (-(1 : ℝ) / 2) = (Real.sqrt u)⁻¹ := by
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by norm_num, Real.rpow_neg hu_pos.le]
    congr 1
    rw [Real.rpow_div_two_eq_sqrt 1 hu_pos.le, Real.rpow_one]
  have hsq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu_pos.le
  have hden_pos : 0 < Real.sqrt u * (1 + Real.sqrt u) := mul_pos hs_pos (by linarith)
  have hkey : (Real.sqrt u)⁻¹ - 1 = -(u - 1) / (Real.sqrt u * (1 + Real.sqrt u)) := by
    have hne : Real.sqrt u ≠ 0 := ne_of_gt hs_pos
    field_simp
    nlinarith [hsq]
  have hu1 : |u - 1| ≤ 6 * v * (1 - v) := by
    have hsub : u - 1 = v ^ 2 + 2 * v * Real.cos θ := by rw [hu]; ring
    rw [hsub]
    have hstep : |v ^ 2 + 2 * v * Real.cos θ| ≤ v ^ 2 + 2 * v := by
      calc |v ^ 2 + 2 * v * Real.cos θ|
          ≤ |v ^ 2| + |2 * v * Real.cos θ| := abs_add_le _ _
        _ = v ^ 2 + 2 * v * |Real.cos θ| := by
              rw [abs_of_nonneg (sq_nonneg v), abs_mul,
                abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * v)]
        _ ≤ v ^ 2 + 2 * v := by
              have hc := Real.abs_cos_le_one θ
              nlinarith [hv0]
    have harith : v ^ 2 + 2 * v ≤ 6 * v * (1 - v) := by nlinarith [hv0, hv]
    linarith
  rw [hrpow]
  calc |(Real.sqrt u)⁻¹ - 1|
      = |u - 1| / (Real.sqrt u * (1 + Real.sqrt u)) := by
        rw [hkey, abs_div, abs_neg, abs_of_pos hden_pos]
    _ ≤ |u - 1| / Real.sqrt u := by
        apply div_le_div_of_nonneg_left (abs_nonneg _) hs_pos
        nlinarith [hs_pos]
    _ ≤ |u - 1| / (1 - v) := by
        exact div_le_div_of_nonneg_left (abs_nonneg _) h1v hs_ge
    _ ≤ 6 * v := by
        rw [div_le_iff₀ h1v]
        linarith [hu1]

theorem abs_phiFun_le_six_mul (v : ℝ) (hv0 : 0 < v) (hv : v ≤ 1 / 2) :
    |(1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1)| ≤ 6 * v := by
  set f : ℝ → ℝ := fun θ => ((1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2)) - 1 with hf
  have hf_cont : Continuous f := by
    rw [hf]
    refine Continuous.sub ?_ continuous_const
    refine Continuous.rpow_const (by fun_prop) ?_
    intro θ
    exact Or.inl (ne_of_gt (one_add_sq_add_two_mul_cos_pos hv0 hv))
  have hbound : ∀ θ, |f θ| ≤ 6 * v := fun θ => abs_rpow_neg_half_sub_one_le hv0 hv
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt Real.two_pi_pos
  have h1 : |∫ θ in (0)..(2 * Real.pi), f θ| ≤ ∫ θ in (0)..(2 * Real.pi), |f θ| :=
    intervalIntegral.abs_integral_le_integral_abs h2pi
  have h2 : (∫ θ in (0)..(2 * Real.pi), |f θ|) ≤ ∫ θ in (0)..(2 * Real.pi), (6 * v) := by
    apply intervalIntegral.integral_mono_on h2pi
    · exact hf_cont.abs.intervalIntegrable _ _
    · exact intervalIntegrable_const
    · intro θ _
      exact hbound θ
  have h3 : (∫ θ in (0)..(2 * Real.pi), (6 * v)) = 2 * Real.pi * (6 * v) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have habs : |∫ θ in (0)..(2 * Real.pi), f θ| ≤ 2 * Real.pi * (6 * v) := by
    linarith [h1, h2, h3.le]
  calc |(1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi), f θ|
      = (1 / (2 * Real.pi)) * |∫ θ in (0)..(2 * Real.pi), f θ| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    _ ≤ (1 / (2 * Real.pi)) * (2 * Real.pi * (6 * v)) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ = 6 * v := by
        field_simp

end Commons.Analysis.Integral