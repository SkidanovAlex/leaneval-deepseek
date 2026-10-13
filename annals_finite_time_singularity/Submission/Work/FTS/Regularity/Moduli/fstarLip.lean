import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity.Moduli

/-- Algebraic key bound: for `z, z' ≥ 0` the factor `|1 - z z'|` appearing in the
difference `F_*(z) - F_*(z')` is dominated by `(1+z)²(1+z')²`. -/
private lemma abs_one_sub_mul_le {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |1 - z * z'| ≤ (1 + z) ^ 2 * (1 + z') ^ 2 := by
  have hzz : 0 ≤ z * z' := mul_nonneg hz hz'
  have hA1 : 1 ≤ (1 + z) * (1 + z') := by nlinarith
  have hmax : |1 - z * z'| ≤ (1 + z) * (1 + z') := by
    by_cases h : z * z' ≤ 1
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - z * z')]
      nlinarith
    · rw [abs_of_neg (by linarith : 1 - z * z' < 0)]
      nlinarith
  have hsq : (1 + z) * (1 + z') ≤ ((1 + z) * (1 + z')) ^ 2 := by nlinarith
  calc |1 - z * z'| ≤ (1 + z) * (1 + z') := hmax
    _ ≤ ((1 + z) * (1 + z')) ^ 2 := hsq
    _ = (1 + z) ^ 2 * (1 + z') ^ 2 := by ring

/-- The exact difference of the profile `F_*(z) = 2z/(1+z)²` factors through the
difference `z - z'` with a bounded coefficient. -/
private lemma fstar_sub {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    Work.FM.Fstar z - Work.FM.Fstar z' =
      2 * (z - z') * (1 - z * z') / ((1 + z) ^ 2 * (1 + z') ^ 2) := by
  have h1 : (1 + z) ^ 2 ≠ 0 := by positivity
  have h2 : (1 + z') ^ 2 ≠ 0 := by positivity
  simp only [Work.FM.Fstar]
  field_simp
  ring

lemma fstarLip {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |Work.FM.Fstar z - Work.FM.Fstar z'| ≤ 2 * |z - z'| := by
  rw [fstar_sub hz hz', abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hden : 0 < (1 + z) ^ 2 * (1 + z') ^ 2 := by positivity
  rw [abs_of_pos hden, div_le_iff₀ hden]
  have hkey : |1 - z * z'| ≤ (1 + z) ^ 2 * (1 + z') ^ 2 := abs_one_sub_mul_le hz hz'
  have h2 : (0 : ℝ) ≤ 2 * |z - z'| := by positivity
  linarith [mul_le_mul_of_nonneg_left hkey h2]

end Work.FTS.Regularity.Moduli
