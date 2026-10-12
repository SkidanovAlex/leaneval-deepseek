import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.phiC_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- **The `1/r²`-difference of the clean bracket.**  For `0 < r_lo ≤ r_hi`, `v_n ∈ [v_lo,v_hi]` and
`r_n, r_x ∈ [r_lo,r_hi]`, the `1/r²`-term of `phiC u v r = v²/S(u,v) − v²/(2r²)` varies by at most
`M²/2·(1/r_lo² − 1/r_hi²)`, `M = max |v_lo| |v_hi|`.

Route: `|v_n²/(2r_n²) − v_n²/(2r_x²)| = (v_n²/2)·|1/r_n² − 1/r_x²|`, `v_n² ≤ M²`, and
`r ↦ 1/r²` is decreasing on `r > 0`, so `|1/r_n² − 1/r_x²| ≤ 1/r_lo² − 1/r_hi²`. -/
theorem phiC_rpart_le {v_lo v_hi r_lo r_hi v_n r_n r_x : ℝ}
    (hrl : 0 < r_lo) (hrlh : r_lo ≤ r_hi) (hvn : v_lo ≤ v_n) (hvn2 : v_n ≤ v_hi)
    (hrn : r_lo ≤ r_n) (hrn2 : r_n ≤ r_hi) (hrx : r_lo ≤ r_x) (hrx2 : r_x ≤ r_hi) :
    |v_n ^ 2 / (2 * r_n ^ 2) - v_n ^ 2 / (2 * r_x ^ 2)|
      ≤ (max |v_lo| |v_hi|) ^ 2 / 2 * (1 / r_lo ^ 2 - 1 / r_hi ^ 2) := by
  -- `M := max |v_lo| |v_hi|` is a nonnegative upper bound for `|v_n|`.
  have hrhi : 0 < r_hi := lt_of_lt_of_le hrl hrlh
  have hM0 : 0 ≤ max |v_lo| |v_hi| := le_trans (abs_nonneg v_lo) (le_max_left _ _)
  have hvnabs : |v_n| ≤ max |v_lo| |v_hi| := by
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le v_lo, le_max_left |v_lo| |v_hi|],
           by linarith [le_abs_self v_hi, le_max_right |v_lo| |v_hi|]⟩
  have hvnsq : v_n ^ 2 ≤ (max |v_lo| |v_hi|) ^ 2 := by
    have h : |v_n| ≤ |(max |v_lo| |v_hi|)| := by rwa [abs_of_nonneg hM0]
    exact sq_le_sq.mpr h
  -- `r ↦ 1/r²` is decreasing on `r > 0`, so both `1/r_n²` and `1/r_x²` lie in
  -- `[1/r_hi², 1/r_lo²]`.
  have hrn0 : 0 < r_n := lt_of_lt_of_le hrl hrn
  have hrx0 : 0 < r_x := lt_of_lt_of_le hrl hrx
  have hnl : 1 / r_n ^ 2 ≤ 1 / r_lo ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hnh : 1 / r_hi ^ 2 ≤ 1 / r_n ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hxl : 1 / r_x ^ 2 ≤ 1 / r_lo ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hxh : 1 / r_hi ^ 2 ≤ 1 / r_x ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hdiff : |1 / r_n ^ 2 - 1 / r_x ^ 2| ≤ 1 / r_lo ^ 2 - 1 / r_hi ^ 2 := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  -- factor the common `v_n²/2` out of the difference
  have hsplit : v_n ^ 2 / (2 * r_n ^ 2) - v_n ^ 2 / (2 * r_x ^ 2)
      = v_n ^ 2 / 2 * (1 / r_n ^ 2 - 1 / r_x ^ 2) := by ring
  rw [hsplit, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ v_n ^ 2 / 2)]
  exact mul_le_mul (by linarith : v_n ^ 2 / 2 ≤ (max |v_lo| |v_hi|) ^ 2 / 2)
    hdiff (abs_nonneg _) (by positivity)

end Work.BoseBogFS
