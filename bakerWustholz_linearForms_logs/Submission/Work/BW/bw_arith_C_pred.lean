import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.elim_Cstep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Nonnegativity of the Baker–Wüstholz constant in the range we need: `n ≥ 1`, `d ≥ 1`.
All factors of `18 · (n+1)! · n^{n+1} · (32d)^{n+2} · log(2nd)` are nonnegative. -/
private lemma C_nonneg {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) :
    0 ≤ BakerWustholz.C n d := by
  unfold BakerWustholz.C
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (2 * (n : ℝ) * d) := by
    apply Real.log_nonneg
    nlinarith
  positivity

/-- The predecessor step for the Baker–Wüstholz constant: raising the rank from `n-1` to `n`
costs at most a factor `d`.

For `n = 1` the constant `C (0) d = 18 · 1! · 0^1 · (32d)^2 · log 0 = 0` vanishes, so the
inequality reads `0 ≤ C 1 d`. For `n ≥ 2` it follows from the sharper elimination estimate
`64 n (n+1) d · C(n-1,d) ≤ C(n,d)` of `elim_Cstep`, since `d ≤ 64 n (n+1) d`. -/
theorem bw_arith_C_pred (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    (d : ℝ) * BakerWustholz.C (n - 1) d ≤ BakerWustholz.C n d := by
  rcases eq_or_lt_of_le hn with hn1 | hn2
  · -- Case `n = 1`: `C 0 d = 0` and `C 1 d ≥ 0`.
    subst hn1
    have hC0 : BakerWustholz.C (1 - 1) d = 0 := by
      unfold BakerWustholz.C
      norm_num
    rw [hC0, mul_zero]
    exact C_nonneg (by norm_num) hd
  · -- Case `n ≥ 2`: sharpen `elim_Cstep` by the obvious `d ≤ 64 n (n+1) d`.
    have hstep := elim_Cstep hn2 hd
    have hCnn : 0 ≤ BakerWustholz.C (n - 1) d := C_nonneg (by omega) hd
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hprod : (2 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
      calc (2 : ℝ) = 1 * 2 := by ring
        _ ≤ (n : ℝ) * ((n : ℝ) + 1) :=
            mul_le_mul hn1' (by linarith) (by norm_num) (by linarith)
    have hcoef : (d : ℝ) ≤ 64 * (n : ℝ) * ((n : ℝ) + 1) * (d : ℝ) := by
      have h1 : (1 : ℝ) ≤ 64 * (n : ℝ) * ((n : ℝ) + 1) := by nlinarith [hprod]
      calc (d : ℝ) = 1 * (d : ℝ) := by ring
        _ ≤ 64 * (n : ℝ) * ((n : ℝ) + 1) * (d : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
    have key : (d : ℝ) * BakerWustholz.C (n - 1) d
        ≤ 64 * (n : ℝ) * ((n : ℝ) + 1) * (d : ℝ) * BakerWustholz.C (n - 1) d :=
      mul_le_mul_of_nonneg_right hcoef hCnn
    linarith [key, hstep]

end Work.BW
