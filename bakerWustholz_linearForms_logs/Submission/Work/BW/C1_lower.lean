import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Numeric lower bound used for step C1 of the Baker–Wüstholz argument.

For `r ≥ 2`, `d ≥ 1`, `h ≥ 1`:
`18874368 · r³ · h · d² ≤ 144 · 2ʳ · 32^(r+1) · r^(r+1) · h · d² · log(2rd)`.

The proof uses the three generous lower bounds
`2ʳ · 32^(r+1) ≥ 2^17 = 131072` (for `r ≥ 2`), `r^(r+1) ≥ r³` (for `r ≥ 1`),
and `log (2rd) ≥ 1` (for `r ≥ 2`, `d ≥ 1`, since `2rd ≥ 4 > 3 > e`). -/
theorem C1_lower {d h r : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) :
    18874368 * (r:ℝ)^3 * (h:ℝ) * (d:ℝ)^2
      ≤ 144 * (2:ℝ)^r * (32:ℝ)^(r+1) * (r:ℝ)^(r+1) * (h:ℝ) * (d:ℝ)^2
          * Real.log (2*(r:ℝ)*(d:ℝ)) := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hrnn : (0:ℝ) ≤ (r:ℝ) := by linarith
  -- log(2rd) ≥ 1  since  2rd ≥ 4 > 3 > exp 1
  have hlog : (1:ℝ) ≤ Real.log (2*(r:ℝ)*(d:ℝ)) := by
    rw [Real.le_log_iff_exp_le (by positivity : (0:ℝ) < 2*(r:ℝ)*(d:ℝ))]
    have h4 : (3:ℝ) ≤ 2*(r:ℝ)*(d:ℝ) := by nlinarith [hr2, hd1]
    linarith [Real.exp_one_lt_three]
  -- 2^r · 32^(r+1) ≥ 2^17 = 131072
  have hpow : (131072:ℝ) ≤ (2:ℝ)^r * (32:ℝ)^(r+1) := by
    have h32 : (32:ℝ)^(r+1) = (2:ℝ)^(5*(r+1)) := by
      rw [show (32:ℝ) = (2:ℝ)^5 by norm_num, ← pow_mul]
    rw [h32, ← pow_add]
    have h17 : (2:ℝ)^17 = 131072 := by norm_num
    rw [← h17]
    exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 17 ≤ r + 5*(r+1))
  -- r³ ≤ r^(r+1)
  have hrpow : (r:ℝ)^3 ≤ (r:ℝ)^(r+1) :=
    pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ (r:ℝ)) (by omega : 3 ≤ r+1)
  -- core inequality, without the common factor h·d²
  have key : (144:ℝ) * 131072 * (r:ℝ)^3
      ≤ 144 * ((2:ℝ)^r * (32:ℝ)^(r+1)) * ((r:ℝ)^(r+1) * Real.log (2*(r:ℝ)*(d:ℝ))) := by
    have hA' : (144:ℝ) * 131072 ≤ 144 * ((2:ℝ)^r * (32:ℝ)^(r+1)) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    have hrD : (r:ℝ)^3 ≤ (r:ℝ)^(r+1) * Real.log (2*(r:ℝ)*(d:ℝ)) := by
      have h2 : (r:ℝ)^(r+1) * 1 ≤ (r:ℝ)^(r+1) * Real.log (2*(r:ℝ)*(d:ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      calc (r:ℝ)^3 ≤ (r:ℝ)^(r+1) := hrpow
        _ = (r:ℝ)^(r+1) * 1 := (mul_one _).symm
        _ ≤ _ := h2
    exact mul_le_mul hA' hrD (by positivity) (by positivity)
  have hcore : (18874368:ℝ) * (r:ℝ)^3
      ≤ 144 * (2:ℝ)^r * (32:ℝ)^(r+1) * (r:ℝ)^(r+1) * Real.log (2*(r:ℝ)*(d:ℝ)) := by
    nlinarith [key]
  have hmult := mul_le_mul_of_nonneg_right hcore (by positivity : (0:ℝ) ≤ (h:ℝ) * (d:ℝ)^2)
  nlinarith [hmult]

end Work.BW
