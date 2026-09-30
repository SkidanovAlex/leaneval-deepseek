import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For `n, d ≥ 1`: `3·d^{n+1}·log 2 ≤ C(n,d)·log 2`.
Proof sketch: it suffices to show `3·d^{n+1} ≤ C(n,d)` (`log 2 > 0`), and
`C(n,d) ≥ 18·2·1·(32d)^{n+2}·(2/3) = 12·(32d)^{n+2}` using `(n+1)! ≥ 2`, `n^{n+1} ≥ 1` and
`log(2nd) ≥ log 2 ≥ 2/3`; finally `12(32d)^{n+2} ≥ 3d^{n+1}` since `4·32^{n+2}·d ≥ 1`. -/
theorem bw_rank1_dpow_le (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    3 * (d : ℝ) ^ (n + 1) * Real.log 2 ≤ BakerWustholz.C n d * Real.log 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2nn : 0 ≤ Real.log 2 := le_of_lt hlog2pos
  have hD : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `(n+1)! ≥ 2`
  have hfact : (2 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    have : (2 : ℕ) ≤ (n + 1).factorial := by
      calc (2 : ℕ) = Nat.factorial 2 := by norm_num
        _ ≤ Nat.factorial (n + 1) := Nat.factorial_le (by omega)
    exact_mod_cast this
  have hNpow : (1 : ℝ) ≤ (n : ℝ) ^ (n + 1) := one_le_pow₀ hN
  have hP : 0 ≤ (32 * (d : ℝ)) ^ (n + 2) := by positivity
  -- `log (2nd) ≥ log 2`
  have hlog : Real.log 2 ≤ Real.log (2 * (n : ℝ) * (d : ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  -- `C(n,d) ≥ 36·(32d)^{n+2}·log 2`
  have hmain : 36 * (32 * (d : ℝ)) ^ (n + 2) * Real.log 2 ≤ BakerWustholz.C n d := by
    unfold BakerWustholz.C
    have hA : (36 : ℝ) ≤ 18 * ↑(n + 1).factorial * (n : ℝ) ^ (n + 1) := by
      nlinarith [hfact, hNpow]
    calc 36 * (32 * (d : ℝ)) ^ (n + 2) * Real.log 2
        ≤ (18 * ↑(n + 1).factorial * (n : ℝ) ^ (n + 1)) * (32 * (d : ℝ)) ^ (n + 2) *
            Real.log 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hP) hlog2nn
      _ ≤ (18 * ↑(n + 1).factorial * (n : ℝ) ^ (n + 1)) * (32 * (d : ℝ)) ^ (n + 2) *
            Real.log (2 * (n : ℝ) * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
  -- `3·d^{n+1} ≤ 36·(32d)^{n+2}·log 2` (`log 2 ≥ 1/2`)
  have hstep2 : 3 * (d : ℝ) ^ (n + 1) ≤ 36 * (32 * (d : ℝ)) ^ (n + 2) * Real.log 2 := by
    have hA : (d : ℝ) ^ (n + 1) ≤ (32 * (d : ℝ)) ^ (n + 2) := by
      have h1 : (d : ℝ) ^ (n + 1) ≤ (d : ℝ) ^ (n + 2) := pow_le_pow_right₀ hD (by omega)
      have h2 : (d : ℝ) ^ (n + 2) ≤ (32 * (d : ℝ)) ^ (n + 2) :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) (n + 2)
      linarith
    have hL : (3 : ℝ) ≤ 36 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [hA, hP, hL]
  have hfinal : 3 * (d : ℝ) ^ (n + 1) ≤ BakerWustholz.C n d := le_trans hstep2 hmain
  exact mul_le_mul_of_nonneg_right hfinal hlog2nn

end Work.BW
