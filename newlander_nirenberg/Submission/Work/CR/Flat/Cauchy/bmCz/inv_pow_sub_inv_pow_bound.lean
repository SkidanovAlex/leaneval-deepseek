import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs

namespace Work.CR.Flat.Cauchy.bmCz

/-- Quantitative comparison of inverse powers: if `X` and `Y` are comparable
(`X ≤ 2Y` and `2Y ≤ 3X`) and `|X - Y| ≤ H`, then the difference of the `m`-th
inverse powers is controlled by `m (3/2)^(m-1) 2^m H / X^(m+1)`. -/
theorem inv_pow_sub_inv_pow_bound {m : ℕ} (hm : 1 ≤ m) {X Y H : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H) (hXY : |X - Y| ≤ H)
    (hYe : X ≤ 2 * Y) (hYu : 2 * Y ≤ 3 * X) :
    |1 / Y ^ m - 1 / X ^ m| ≤ ((m : ℝ) * (3 / 2) ^ (m - 1) * 2 ^ m) * H / X ^ (m + 1) := by
  have hmR : (0:ℝ) ≤ (m:ℝ) := by positivity
  have hXc : X ≠ 0 := ne_of_gt hX
  have hYc : Y ≠ 0 := ne_of_gt hY
  have hXm : (0:ℝ) < X^m := pow_pos hX m
  have hYm : (0:ℝ) < Y^m := pow_pos hY m
  have hD : (0:ℝ) < X^m * Y^m := mul_pos hXm hYm
  -- express the difference of inverse powers with a common denominator
  have hkey : 1 / Y^m - 1 / X^m = (X^m - Y^m) / (X^m * Y^m) := by
    rw [one_div, one_div, inv_sub_inv (pow_ne_zero m hYc) (pow_ne_zero m hXc),
      mul_comm (Y^m) (X^m)]
  rw [hkey, abs_div, abs_of_pos hD]
  have hmaxnn : (0:ℝ) ≤ max X Y := le_of_lt (lt_of_lt_of_le hX (le_max_left X Y))
  -- numerator bound: |X^m - Y^m| ≤ H * m * (3/2)^(m-1) * X^(m-1)
  have hnum : |X^m - Y^m| ≤ H * (m:ℝ) * (3/2)^(m-1) * X^(m-1) := by
    have hbase := abs_pow_sub_pow_le X Y m
    rw [abs_of_pos hX, abs_of_pos hY] at hbase
    have hmax : max X Y ≤ (3:ℝ)/2 * X := by
      rw [max_le_iff]
      exact ⟨by nlinarith [hX], by nlinarith [hYu]⟩
    have hpow : max X Y ^ (m-1) ≤ ((3:ℝ)/2 * X)^(m-1) :=
      pow_le_pow_left₀ hmaxnn hmax _
    calc |X^m - Y^m| ≤ |X - Y| * (m:ℝ) * max X Y ^ (m-1) := hbase
      _ ≤ H * (m:ℝ) * max X Y ^ (m-1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hXY hmR) (pow_nonneg hmaxnn _)
      _ ≤ H * (m:ℝ) * ((3:ℝ)/2 * X)^(m-1) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hH hmR)
      _ = H * (m:ℝ) * (3/2)^(m-1) * X^(m-1) := by rw [mul_pow]; ring
  have hNb_nonneg : (0:ℝ) ≤ H * (m:ℝ) * (3/2)^(m-1) * X^(m-1) :=
    mul_nonneg (mul_nonneg (mul_nonneg hH hmR) (pow_nonneg (by norm_num) _))
      (pow_nonneg (le_of_lt hX) _)
  -- denominator lower bound: X^(2m)/2^m ≤ X^m * Y^m
  have hYge : X/2 ≤ Y := by linarith [hYe]
  have hYp : (X/2)^m ≤ Y^m := pow_le_pow_left₀ (by positivity) hYge m
  have hX2m : X^(2*m) = X^m * X^m := by rw [show 2*m = m+m by ring, pow_add]
  have heq : X^m * (X/2)^m = X^(2*m)/2^m := by
    rw [div_pow, hX2m]; ring
  have hDbl : X^(2*m)/2^m ≤ X^m * Y^m := by
    calc X^(2*m)/2^m = X^m * (X/2)^m := heq.symm
      _ ≤ X^m * Y^m := mul_le_mul_of_nonneg_left hYp (le_of_lt hXm)
  have hDbl_pos : (0:ℝ) < X^(2*m)/2^m := by positivity
  calc |X^m - Y^m| / (X^m * Y^m)
      ≤ (H * (m:ℝ) * (3/2)^(m-1) * X^(m-1)) / (X^m * Y^m) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hD)
    _ ≤ (H * (m:ℝ) * (3/2)^(m-1) * X^(m-1)) / (X^(2*m)/2^m) :=
        div_le_div_of_nonneg_left hNb_nonneg hDbl_pos hDbl
    _ = ((m:ℝ)*(3/2)^(m-1)*2^m)*H/X^(m+1) := by
        have hX2m' : X^(2*m) = X^(m-1) * X^(m+1) := by
          rw [← pow_add]; congr 1; omega
        rw [hX2m']
        field_simp

end Work.CR.Flat.Cauchy.bmCz
