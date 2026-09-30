import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-! ### `h = ph h'(L) v ≥ 19`

BW §13 needs the height parameter `h = [h'(L) + v log 2]` to be at least `19` (see e.g.
`num_13`, `num_17`, `num_T`, `num_kum`, `Mu_ge_Me`, `aux_poly_arith`, which all take `19 ≤ h`).

The standing assumptions of §11 supply `X(n,d) ≤ h'(L)`, where
`X(n,d) = log C(n,d) − n log d − log(n+d)` and `C(n,d) = 18 (n+1)! n^{n+1} (32d)^{n+2} log(2nd)`.
The true value of `X` is at least `19.85` (minimum at `(n,d) = (2,1)`); we prove the rounded
bound `19 ≤ X(n,d)` for `2 ≤ n`, `1 ≤ d` and deduce `19 ≤ ph (h'(L)) v` from
`ph H v = ⌊H + v log 2⌋₊` (the `v log 2` term is nonnegative).

The argument for `19 ≤ X(n,d)` expands

`X(n,d) = log 18 + log((n+1)!) + (n+1) log n + (n+2) log 32 + 2 log d + log log(2nd) − log(n+d)`

(all factors positive), and uses

* `(n+1)! ≥ 2 · 3^{n−1}` (each of `4, …, n+1` is at least `3`), so `log((n+1)!) ≥ log 2 + (n−1) log 3`;
* `log(n+d) ≤ log(2nd) = log 2 + log n + log d` (as `n + d ≤ 2nd`);
* `log d ≥ 0`, `log log(2nd) ≥ 0` (`2nd ≥ 4 > e`), `log 32 = 5 log 2`, `log 18 = log 2 + 2 log 3`,
  `n log n ≥ 2 log 2`, `(n+2) log 32 ≥ 20 log 2`.

This leaves `X(n,d) ≥ 23 log 2 + 3 log 3 ≥ 23·0.6931471803 + 3·1.0986122885 > 19`. -/

/-- `2 · 3^m ≤ (m+2)!`; equivalently `(n+1)! ≥ 2·3^{n-1}` for `n ≥ 2`. -/
private theorem factorial_ge (m : ℕ) : 2 * 3 ^ m ≤ (m + 2).factorial := by
  induction m with
  | zero => norm_num
  | succ k ih =>
    have h1 : (k + 3).factorial = (k + 3) * (k + 2).factorial := Nat.factorial_succ (k + 2)
    have h2 : (3:ℕ) ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
    rw [h1, h2]
    calc 2 * (3 ^ k * 3) = 3 * (2 * 3 ^ k) := by ring
      _ ≤ 3 * (k + 2).factorial := Nat.mul_le_mul_left 3 ih
      _ ≤ (k + 3) * (k + 2).factorial := Nat.mul_le_mul_right _ (by omega)

/-- `2 · 3^{n-1} ≤ (n+1)!` for `n ≥ 2`. -/
private theorem factorial_ge' (n : ℕ) (hn : 2 ≤ n) : 2 * 3 ^ (n - 1) ≤ (n + 1).factorial := by
  have h := factorial_ge (n - 1)
  have hh : n - 1 + 2 = n + 1 := by omega
  rwa [hh] at h

/-- Expansion of `X(n,d) = log C(n,d) − n log d − log(n+d)` into a sum of logarithms
(all factors positive for `n, d ≥ 1`; the `n log d` term is absorbed into `(n+2) log d`). -/
private lemma Xbw_eq (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    Xbw n d = Real.log 18 + Real.log ((n + 1).factorial : ℝ) + ((n : ℝ) + 1) * Real.log (n : ℝ)
      + ((n : ℝ) + 2) * Real.log 32 + 2 * Real.log (d : ℝ)
      + Real.log (Real.log (2 * (n : ℝ) * (d : ℝ))) - Real.log ((n : ℝ) + (d : ℝ)) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hn0 : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le one_pos hn1
  have hd0 : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le one_pos hd1
  have hL0 : (0:ℝ) < Real.log (2 * (n:ℝ) * (d:ℝ)) := by
    apply Real.log_pos; nlinarith
  rw [Xbw, BakerWustholz.C,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num : (32:ℝ) ≠ 0) (by positivity : (d:ℝ) ≠ 0)]
  push_cast
  ring

/-- `X(n,d) = log C(n,d) − n log d − log(n+d) ≥ 19` for `n ≥ 2`, `d ≥ 1` (BW §13;
the true minimum is `≈ 19.85` at `(n,d) = (2,1)`, so this is sharp to within rounding). -/
theorem Xbw_ge_nineteen (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) : 19 ≤ Xbw n d := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h3 : (1.0986122885:ℝ) < Real.log 3 := Real.log_three_gt_d9
  have hlog2 : (0:ℝ) < Real.log 2 := by linarith
  have hlog3 : (0:ℝ) < Real.log 3 := by linarith
  have hlogn : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hn2
  have hlogd : (0:ℝ) ≤ Real.log (d:ℝ) := Real.log_nonneg hd1
  have h18 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
    have hh : (18:ℝ) = 2 * 3^2 := by norm_num
    rw [hh, Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    have hh : (32:ℝ) = 2^5 := by norm_num
    rw [hh, Real.log_pow]; norm_num
  have hfac : Real.log 2 + ((n:ℝ) - 1) * Real.log 3 ≤ Real.log ((n+1).factorial : ℝ) := by
    have hpos : (0:ℝ) < 2 * 3 ^ (n - 1) := by positivity
    have hle : (2:ℝ) * 3 ^ (n - 1) ≤ ((n + 1).factorial : ℝ) := by
      exact_mod_cast factorial_ge' n hn
    have h := Real.log_le_log hpos hle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
    have hcast : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
      rw [Nat.cast_sub hn1]; norm_num
    rw [hcast] at h
    linarith
  have hsum : Real.log ((n:ℝ) + (d:ℝ)) ≤ Real.log 2 + Real.log (n:ℝ) + Real.log (d:ℝ) := by
    have h1 : (0:ℝ) < (n:ℝ) + (d:ℝ) := by linarith
    have h2' : (n:ℝ) + (d:ℝ) ≤ 2 * (n:ℝ) * (d:ℝ) := by nlinarith
    calc Real.log ((n:ℝ) + (d:ℝ)) ≤ Real.log (2 * (n:ℝ) * (d:ℝ)) := Real.log_le_log h1 h2'
      _ = Real.log 2 + Real.log (n:ℝ) + Real.log (d:ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul (by positivity) (by positivity)]
  have hLL : (0:ℝ) ≤ Real.log (Real.log (2 * (n:ℝ) * (d:ℝ))) := by
    apply Real.log_nonneg
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith [Real.exp_one_lt_three]
  have hnlogn : 2 * Real.log 2 ≤ (n:ℝ) * Real.log (n:ℝ) :=
    mul_le_mul hn2 hlogn (le_of_lt hlog2) (by linarith)
  have hA : 20 * Real.log 2 ≤ ((n:ℝ) + 2) * (5 * Real.log 2) := by nlinarith
  rw [Xbw_eq n d hn1 hd, h18, h32]
  nlinarith [h2, h3, hfac, hnlogn, hsum, hLL, hlogd, hlogn, hA]

/-- The height parameter `h = ph h'(L) v` of BW §13 is at least `19`. -/
theorem ph_ge_nineteen {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (φ : K →+* ℂ) (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (v : ℕ)
    (hst : Standing φ α b k c) :
    19 ≤ ph (hL b (Module.finrank ℚ K)) v := by
  have hn : 2 ≤ n := hst.1
  have hd : 1 ≤ Module.finrank ℚ K := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    omega
  have hX : (19:ℝ) ≤ Xbw n (Module.finrank ℚ K) := by
    exact_mod_cast Xbw_ge_nineteen n (Module.finrank ℚ K) hn hd
  have hle : Xbw n (Module.finrank ℚ K) ≤ hL b (Module.finrank ℚ K) := hst.2.2.2.2.2.2.1
  have h19 : (19:ℝ) ≤ hL b (Module.finrank ℚ K) := le_trans hX hle
  have hv : (0:ℝ) ≤ (v:ℝ) * Real.log 2 := by
    have : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hmain : ((19:ℕ):ℝ) ≤ hL b (Module.finrank ℚ K) + v * Real.log 2 := by
    push_cast
    linarith
  exact Nat.le_floor hmain

end Work.BW
