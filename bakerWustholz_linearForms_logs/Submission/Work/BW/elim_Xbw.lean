import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The elementary numerical core of `elim_Xbw`: with the Baker–Wüstholz constant
`C(n,d) = 18 (n+1)! n^{n+1} (32d)^{n+2} log(2nd)` one has
`n^n · d^{n+1} · (n+d) ≤ C(n,d)` for `n ≥ 2`, `d ≥ 1`.

The bound has enormous slack. Dividing by `n^n d^{n+1}` it is equivalent to
`n + d ≤ 18 (n+1)! n · 32^{n+2} · d · log(2nd)`; here `n + d ≤ 2nd`, and
`18 (n+1)! 32^{n+2} log(2nd) ≥ 18 · 6 · 32^4 · 1 ≥ 2` since `n + 1 ≥ 3` and `2nd ≥ 4 > e`. -/
private lemma C_dominates_prod {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    (n : ℝ) ^ n * (d : ℝ) ^ (n + 1) * ((n : ℝ) + (d : ℝ)) ≤ BakerWustholz.C n d := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  -- `(n+1)! ≥ 3! = 6`
  have hfact : (6 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    have h3 : (3 : ℕ) ≤ n + 1 := by omega
    have h := Nat.factorial_le h3
    norm_num at h
    exact_mod_cast h
  -- `32^(n+2) ≥ 32^4`
  have h32 : (32 : ℝ) ^ 4 ≤ (32 : ℝ) ^ (n + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  -- `log (2nd) ≥ log 4 ≥ 1`
  have harg : (4 : ℝ) ≤ 2 * (n : ℝ) * (d : ℝ) := by nlinarith
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h := Real.log_two_gt_d9
    have h2 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h2]; linarith
  have hlog : (1 : ℝ) ≤ Real.log (2 * (n : ℝ) * (d : ℝ)) :=
    le_trans hlog4 (Real.log_le_log (by norm_num) harg)
  -- the cofactor `18 (n+1)! 32^{n+2} log(2nd)` is `≥ 2`
  have hkey : (2 : ℝ) ≤
      18 * ((n + 1).factorial : ℝ) * (32 : ℝ) ^ (n + 2) * Real.log (2 * (n : ℝ) * (d : ℝ)) := by
    calc (2 : ℝ) ≤ 18 * 6 * 32 ^ 4 * 1 := by norm_num
      _ ≤ 18 * ((n + 1).factorial : ℝ) * (32 : ℝ) ^ (n + 2) *
            Real.log (2 * (n : ℝ) * (d : ℝ)) := by gcongr
  rw [BakerWustholz.C]
  -- `n + d ≤ 2 n d` for `n, d ≥ 1`
  have hnd : (n : ℝ) + (d : ℝ) ≤ 2 * (n : ℝ) * (d : ℝ) := by nlinarith
  have hA : (0 : ℝ) ≤ (n : ℝ) ^ n * (d : ℝ) ^ (n + 1) := by positivity
  calc (n : ℝ) ^ n * (d : ℝ) ^ (n + 1) * ((n : ℝ) + (d : ℝ))
      ≤ (n : ℝ) ^ n * (d : ℝ) ^ (n + 1) * (2 * (n : ℝ) * (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hnd hA
    _ = 2 * (n : ℝ) ^ (n + 1) * (d : ℝ) ^ (n + 2) := by rw [pow_succ, pow_succ]; ring
    _ = (n : ℝ) ^ (n + 1) * (d : ℝ) ^ (n + 2) * 2 := by ring
    _ ≤ (n : ℝ) ^ (n + 1) * (d : ℝ) ^ (n + 2) *
          (18 * ((n + 1).factorial : ℝ) * (32 : ℝ) ^ (n + 2) *
            Real.log (2 * (n : ℝ) * (d : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 18 * ((n + 1).factorial : ℝ) * (n : ℝ) ^ (n + 1) * (32 * (d : ℝ)) ^ (n + 2) *
          Real.log (2 * (n : ℝ) * (d : ℝ)) := by rw [mul_pow]; ring

theorem elim_Xbw {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    (n : ℝ) * Real.log n + Real.log d ≤ Work.BW.Xbw n d := by
  -- Exponentiate the target: it suffices to compare `n^n · d^{n+1} · (n+d)` with `C(n,d)`.
  have hmain := C_dominates_prod hn hd
  have hpos : (0 : ℝ) < (n : ℝ) ^ n * (d : ℝ) ^ (n + 1) * ((n : ℝ) + (d : ℝ)) := by
    have hn1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hd1 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hlogm := Real.log_le_log hpos hmain
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlogm
  rw [Work.BW.Xbw]
  push_cast at hlogm ⊢
  linarith

end Work.BW
