import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Commons.Analysis.SpecialFunctions.Log.log_strip_bound_A_nonneg

namespace Commons.Analysis.SpecialFunctions.Log

private lemma log_ge_one_sub_inv (t : ℝ) (ht : 0 < t) : 1 - 1 / t ≤ Real.log t := by
  have hle : Real.log (t⁻¹) ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  have hneg : -Real.log t ≤ t⁻¹ - 1 := by
    simpa [Real.log_inv] using hle
  have hb : 1 - t⁻¹ ≤ Real.log t := by linarith
  simpa [one_div] using hb

theorem log_strip_bound_B_nonneg (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) :
    Real.log 3 + (3 : ℝ) / 2 - Real.log x - (1 : ℝ) / x - (1 : ℝ) / (2 * x ^ 2) - (1 : ℝ) / (2 * x) ≥ 0 := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hC : Real.log x + (3 : ℝ) / (2 * x) + (1 : ℝ) / (2 * x ^ 2) ≤ Real.log 3 + (3 : ℝ) / 2 := by
    by_cases hx2' : x ≤ 2
    · -- Case A: 1 ≤ x ≤ 2. Show C(x) ≤ 2 ≤ log 3 + 3/2.
      have hlogx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hxpos
      have hsub : 0 ≤ x - 1 := sub_nonneg.mpr hx1
      have hqpos : 0 ≤ -2 * x ^ 2 + 4 * x + 1 := by
        have hid : -2 * x ^ 2 + 4 * x + 1 = 3 - 2 * (x - 1) ^ 2 := by ring
        rw [hid]
        have hd1 : x - 1 ≤ 1 := by linarith
        nlinarith [sq_nonneg (x - 1)]
      have hprod : 0 ≤ (x - 1) * (-2 * x ^ 2 + 4 * x + 1) := mul_nonneg hsub hqpos
      have h2x2 : 0 < (2 : ℝ) * x ^ 2 := by positivity
      have hpoly : (x - 1) + (3 : ℝ) / (2 * x) + (1 : ℝ) / (2 * x ^ 2) ≤ 2 := by
        have hnon : 0 ≤ 2 - ((x - 1) + (3 : ℝ) / (2 * x) + (1 : ℝ) / (2 * x ^ 2)) := by
          have hfac' : (x - 1) * (-2 * x ^ 2 + 4 * x + 1) =
              (2 : ℝ) * x ^ 2 * (2 - ((x - 1) + (3 : ℝ) / (2 * x) + (1 : ℝ) / (2 * x ^ 2))) := by
            field_simp [hxne]
            ring
          have hmul : 0 ≤ (2 : ℝ) * x ^ 2 * (2 - ((x - 1) + (3 : ℝ) / (2 * x) + (1 : ℝ) / (2 * x ^ 2))) := by
            rwa [← hfac']
          exact nonneg_of_mul_nonneg_right hmul h2x2
        linarith
      have hA1 : Real.log x + (3 : ℝ) / (2 * x) + (1 : ℝ) / (2 * x ^ 2) ≤ 2 := by
        linarith
      have hlog3 : (1 : ℝ) / 2 ≤ Real.log 3 := by
        have hb := log_ge_one_sub_inv (3 : ℝ) (by norm_num : 0 < (3 : ℝ))
        linarith
      have h2le : (2 : ℝ) ≤ Real.log 3 + (3 : ℝ) / 2 := by linarith
      linarith
    · -- Case B: 2 < x ≤ 8. Show C(x) ≤ C(8) ≤ log 3 + 3/2.
      have hxge2 : 2 ≤ x := le_of_lt (lt_of_not_ge hx2')
      have htpos : 0 < (8 : ℝ) / x := by positivity
      have hb8 : 1 - x / 8 ≤ Real.log ((8 : ℝ) / x) := by
        have hg := log_ge_one_sub_inv ((8 : ℝ) / x) htpos
        have hsim : 1 - 1 / ((8 : ℝ) / x) = 1 - x / 8 := by
          field_simp [hxne]
        rwa [hsim] at hg
      have hlog8x : Real.log ((8 : ℝ) / x) = Real.log 8 - Real.log x :=
        Real.log_div (by norm_num : (8 : ℝ) ≠ 0) hxne
      have hlogge : 1 - x / 8 ≤ Real.log 8 - Real.log x := by
        rwa [hlog8x] at hb8
      have hR : 0 ≤ (1 - x / 8) + (3 : ℝ) / 16 + (1 : ℝ) / 128 - (3 : ℝ) / (2 * x) - (1 : ℝ) / (2 * x ^ 2) := by
        have hN : 0 ≤ (8 - x) * (16 * x ^ 2 - 25 * x - 8) := by
          have h81 : 0 ≤ 8 - x := sub_nonneg.mpr hx2
          have hq : 0 ≤ 16 * x ^ 2 - 25 * x - 8 := by
            have hid : 16 * x ^ 2 - 25 * x - 8 = (x - 2) * (16 * x + 7) + 6 := by ring
            rw [hid]
            have hm : 0 ≤ (x - 2) * (16 * x + 7) := mul_nonneg (sub_nonneg.mpr hxge2) (by positivity)
            linarith
          exact mul_nonneg h81 hq
        have hden : 0 < (128 : ℝ) * x ^ 2 := by positivity
        have heq : (1 - x / 8) + (3 : ℝ) / 16 + (1 : ℝ) / 128 - (3 : ℝ) / (2 * x) - (1 : ℝ) / (2 * x ^ 2) =
            ((8 - x) * (16 * x ^ 2 - 25 * x - 8)) / ((128 : ℝ) * x ^ 2) := by
          field_simp [hxne]
          ring
        rw [heq]
        exact div_nonneg hN (le_of_lt hden)
      have hB1 : Real.log x + (3 : ℝ) / (2 * x) + (1 : ℝ) / (2 * x ^ 2) ≤
          Real.log 8 + (3 : ℝ) / 16 + (1 : ℝ) / 128 := by
        linarith
      have hlog83 : Real.log ((8 : ℝ) / 3) = Real.log 8 - Real.log 3 :=
        Real.log_div (by norm_num : (8 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)
      have hfrac : ((5 : ℝ) / 3) * ((8 : ℝ) / 5) = (8 : ℝ) / 3 := by norm_num
      have hprod : Real.log (((5 : ℝ) / 3) * ((8 : ℝ) / 5)) = Real.log ((5 : ℝ) / 3) + Real.log ((8 : ℝ) / 5) := by
        exact Real.log_mul (by norm_num : (5 : ℝ) / 3 ≠ 0) (by norm_num : (8 : ℝ) / 5 ≠ 0)
      have hlog83eq : Real.log ((8 : ℝ) / 3) = Real.log ((5 : ℝ) / 3) + Real.log ((8 : ℝ) / 5) := by
        rw [← hfrac]
        exact hprod
      have hle53 : Real.log ((5 : ℝ) / 3) ≤ (2 : ℝ) / 3 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (5 : ℝ) / 3)
        linarith
      have hle85 : Real.log ((8 : ℝ) / 5) ≤ (3 : ℝ) / 5 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (8 : ℝ) / 5)
        linarith
      have hlog83le : Real.log 8 - Real.log 3 ≤ (167 : ℝ) / 128 := by
        have hle : Real.log ((8 : ℝ) / 3) ≤ (19 : ℝ) / 15 := by
          rw [hlog83eq]
          linarith
        have h1915 : (19 : ℝ) / 15 ≤ (167 : ℝ) / 128 := by norm_num
        rw [← hlog83]
        exact le_trans hle h1915
      have hC8 : Real.log 8 + (3 : ℝ) / 16 + (1 : ℝ) / 128 ≤ Real.log 3 + (3 : ℝ) / 2 := by
        linarith
      linarith
  rw [show Real.log 3 + (3 : ℝ) / 2 - Real.log x - (1 : ℝ) / x - (1 : ℝ) / (2 * x ^ 2) - (1 : ℝ) / (2 * x) =
      Real.log 3 + (3 : ℝ) / 2 - (Real.log x + (3 : ℝ) / (2 * x) + (1 : ℝ) / (2 * x ^ 2)) by
    field_simp [hxne]
    ring]
  exact sub_nonneg.mpr hC

end Commons.Analysis.SpecialFunctions.Log