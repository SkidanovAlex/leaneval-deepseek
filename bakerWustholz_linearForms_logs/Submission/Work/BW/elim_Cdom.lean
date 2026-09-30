import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Dominance of the Baker–Wüstholz constant over the `d^{n-1}` factor in the elimination
step: for `n ≥ 2` and `d ≥ 1` the constant `C (n-1) d` dominates `(d)^{n-1}`.

Written out, `C (n-1) d = 18 · n! · (n-1)^n · (32d)^{n+1} · log(2(n-1)d)`. Splitting
`(32d)^{n+1} = 32^{n+1} · d^2 · (32d)^{n-1}`... more precisely
`(32d)^{n+1} = 32^{n+1} · d^{n+1}` and `d^{n+1} = d^{n-1} · d^2`, so
`C (n-1) d = (d^{n-1}) · K` with
`K = 18 · n! · (n-1)^n · 32^{n+1} · d^2 · log(2(n-1)d) ≥ 18·2·1·32^3·1·(1/2) = 589824 ≥ 1`,
using `n! ≥ 2`, `(n-1)^n ≥ 1`, `32^{n+1} ≥ 32^3`, `d^2 ≥ 1` and `log(2(n-1)d) ≥ log 2 ≥ 1/2`. -/
theorem elim_Cdom {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    (d : ℝ) ^ (n - 1) ≤ BakerWustholz.C (n - 1) d := by
  have hn1 : 1 ≤ n := by omega
  have hN1 : 1 ≤ n - 1 := by omega
  have e1 : n - 1 + 1 = n := by omega
  have e2 : n - 1 + 2 = n + 1 := by omega
  rw [BakerWustholz.C, e1, e2]
  -- `n! ≥ 2`
  have hfac : (2 : ℝ) ≤ (n.factorial : ℝ) := by
    have : 2 ≤ n.factorial := by
      have h := Nat.self_le_factorial n
      omega
    exact_mod_cast this
  -- `n - 1 ≥ 1`
  have hNm : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hN1
  -- `(n - 1)^n ≥ 1`
  have hNn : (1 : ℝ) ≤ (((n - 1 : ℕ) : ℝ)) ^ n := one_le_pow₀ hNm
  -- `32^(n+1) ≥ 32^3`
  have h32 : (32 : ℝ) ^ 3 ≤ (32 : ℝ) ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  -- `d ≥ 1`
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  -- `d^2 ≥ 1`
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hd1
  -- `log 2 ≥ 1/2`
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  -- the log argument is `≥ 2`
  have harg2 : (2 : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ) := by
    have h3 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * (d : ℝ) := by
      simpa using mul_le_mul hNm hd1 (by norm_num) (by linarith)
    linarith
  have hlogL : (1 / 2 : ℝ) ≤ Real.log (2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ)) :=
    le_trans hlog2 (Real.log_le_log (by norm_num) harg2)
  -- the cofactor `K` is `≥ 1`
  have key : (1 : ℝ) ≤ 18 * (n.factorial : ℝ) * (((n - 1 : ℕ) : ℝ) ^ n) * (32 : ℝ) ^ (n + 1) *
      (d : ℝ) ^ 2 * Real.log (2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ)) := by
    calc (1 : ℝ) ≤ 18 * 2 * 1 * 32 ^ 3 * 1 * (1 / 2) := by norm_num
      _ ≤ 18 * (n.factorial : ℝ) * (((n - 1 : ℕ) : ℝ) ^ n) * (32 : ℝ) ^ (n + 1) * (d : ℝ) ^ 2 *
          Real.log (2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ)) := by
          gcongr
  have hA : (0 : ℝ) ≤ (d : ℝ) ^ (n - 1) := by positivity
  have hpow : (d : ℝ) ^ (n + 1) = (d : ℝ) ^ (n - 1) * (d : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  calc (d : ℝ) ^ (n - 1) = (d : ℝ) ^ (n - 1) * 1 := by ring
    _ ≤ (d : ℝ) ^ (n - 1) * (18 * (n.factorial : ℝ) * (((n - 1 : ℕ) : ℝ) ^ n) *
          (32 : ℝ) ^ (n + 1) * (d : ℝ) ^ 2 *
          Real.log (2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ))) := mul_le_mul_of_nonneg_left key hA
    _ = 18 * (n.factorial : ℝ) * (((n - 1 : ℕ) : ℝ) ^ n) * (32 * (d : ℝ)) ^ (n + 1) *
          Real.log (2 * ((n - 1 : ℕ) : ℝ) * (d : ℝ)) := by
        rw [mul_pow, hpow]; ring

end Work.BW
