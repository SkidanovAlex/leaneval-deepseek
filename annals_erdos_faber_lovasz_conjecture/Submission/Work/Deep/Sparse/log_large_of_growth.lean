import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic

/-!
# A growth-rate consequence: `10^6 (log (x+2))^8 ≤ x` forces `log (x+2) ≥ 44`

This module proves `Work.Deep.Sparse.log_large_of_growth`.  It is used in
`Work.Deep.Sparse.concentration_ncp`, where `10^6 (log (D+2))^8 ≤ D` for a degree bound `D`
and one needs `log (D+2) ≥ 44` (so that `(log (D+2))^4/5000` dominates `log (4 D^6)`).

The proof is elementary.  Put `L = log (x+2)`.  Since `1 ≤ x` we have `L > 1`, and
`exp L = x + 2`, so `x < exp L`.  From the hypothesis and monotonicity of `log`,

`6 * log 10 + 8 * log L = log (10^6 * L^8) ≤ log x < L`.   (★)

If `L ≤ 8`, then (★) gives `8 * log L < 8 - 6 * log 10 < 0` because `6 * log 10 > 8`
(i.e. `exp 8 < 10^6`), hence `L < 1`, a contradiction.

If `8 < L`, then `log L - log 44 = log (L/44)` and the elementary bound
`log y ≤ y - 1` yield the monotonicity of `t ↦ t - 8 log t` on `[8,∞)`, so (★) gives

`6 * log 10 + 8 * log 44 < 44`,

i.e. `log (10^6 * 44^8) < 44 = log (exp 44)`, hence `10^6 * 44^8 < exp 44`.  This contradicts
the numerical fact `exp 44 ≤ 10^6 * 44^8`.

The only analytic input is `Real.exp_bound'` (Taylor expansion with explicit tail), which
gives `exp 1 ≤ 68/25`; the resulting numerical inequalities are checked by exact integer
arithmetic.
-/

namespace Work.Deep.Sparse

/-- `exp 1 ≤ 68/25 = 2.72`, from the Taylor expansion of `exp` with an explicit tail bound
(`Real.exp_bound'` with `n = 8`). -/
lemma exp_one_le_68_div_25 : Real.exp 1 ≤ (68 : ℝ) / 25 := by
  have h := Real.exp_bound' (x := 1) (by norm_num) (le_refl 1) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- `exp 44 ≤ 10^6 * 44^8` (the numerical threshold of `log_large_of_growth`). -/
lemma exp_44_le_10pow6_mul_44pow8 : Real.exp 44 ≤ (10 : ℝ) ^ 6 * 44 ^ 8 := by
  have h1 : Real.exp 44 = (Real.exp 1) ^ 44 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  have h2 : (Real.exp 1) ^ 44 ≤ ((68 : ℝ) / 25) ^ 44 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_le_68_div_25 44
  refine h2.trans ?_
  rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < 25 ^ 44)]
  have h : (68 : ℕ) ^ 44 ≤ (10 : ℕ) ^ 6 * 44 ^ 8 * 25 ^ 44 := by norm_num
  exact_mod_cast h

/-- `exp 8 < 10^6`, equivalently `6 * log 10 > 8`. -/
lemma exp_eight_lt_10pow6 : Real.exp 8 < (10 : ℝ) ^ 6 := by
  have h1 : Real.exp 8 = (Real.exp 1) ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  have h2 : (Real.exp 1) ^ 8 ≤ ((68 : ℝ) / 25) ^ 8 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_le_68_div_25 8
  refine lt_of_le_of_lt h2 ?_
  norm_num

lemma log_large_of_growth {x : ℝ} (hx : 1 ≤ x)
    (h : (10 : ℝ) ^ 6 * (Real.log (x + 2)) ^ 8 ≤ x) : 44 ≤ Real.log (x + 2) := by
  set L : ℝ := Real.log (x + 2) with hLdef
  have hx2 : 0 < x + 2 := by linarith
  have hLpos : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (by linarith)
  have hL1 : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt hx2]
    have : Real.exp 1 < 3 := lt_of_le_of_lt exp_one_le_68_div_25 (by norm_num)
    linarith
  -- (★) : `log (10^6 * L^8) ≤ log x < L`
  have hkey : 6 * Real.log 10 + 8 * Real.log L < L := by
    have hL8pos : (0 : ℝ) < (10 : ℝ) ^ 6 * L ^ 8 := by positivity
    have h1 : Real.log ((10 : ℝ) ^ 6 * L ^ 8) ≤ Real.log x :=
      Real.log_le_log hL8pos h
    have h2 : Real.log x < L := by
      have hxexp : x < Real.exp L := by
        have : Real.exp L = x + 2 := by rw [hLdef]; exact Real.exp_log hx2
        rw [this]; linarith
      calc Real.log x < Real.log (Real.exp L) := Real.log_lt_log (by linarith) hxexp
        _ = L := Real.log_exp L
    have h3 : Real.log ((10 : ℝ) ^ 6 * L ^ 8) = 6 * Real.log 10 + 8 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow (10 : ℝ) 6, Real.log_pow L 8]
      push_cast
      ring
    linarith
  by_contra hcon
  have hcon' : L < 44 := not_le.mp hcon
  have hlog10 : 8 < 6 * Real.log 10 := by
    have h2 := Real.log_lt_log (Real.exp_pos 8) exp_eight_lt_10pow6
    rw [Real.log_exp, Real.log_pow (10 : ℝ) 6] at h2
    push_cast at h2
    linarith
  rcases le_or_gt L 8 with hL8 | hL8
  · -- `L ≤ 8` forces `L < 1`, contradicting `1 < L`
    have h8logL : 8 * Real.log L < 0 := by linarith
    have h1 : Real.log L < Real.log 1 := by rw [Real.log_one]; linarith
    have h2 : L < 1 := (Real.log_lt_log_iff hLpos zero_lt_one).mp h1
    linarith
  · -- `8 < L`: `t ↦ t - 8 log t` is monotone on `[8,∞)`
    have hlogle : Real.log 44 - Real.log L ≤ 44 / L - 1 := by
      have hpos : 0 < 44 / L := by positivity
      have h' := Real.log_le_sub_one_of_pos hpos
      rwa [Real.log_div (by norm_num) (ne_of_gt hLpos)] at h'
    have hbound : 8 * (Real.log 44 - Real.log L) ≤ 44 - L := by
      have h8L : 8 / L ≤ 1 := (div_le_one hLpos).mpr (by linarith)
      have heq : 8 * (Real.log 44 - Real.log L) ≤ 8 * (44 / L - 1) :=
        mul_le_mul_of_nonneg_left hlogle (by norm_num)
      have hval : 8 * (44 / L - 1) = (44 - L) * (8 / L) := by field_simp
      have h' : (44 - L) * (8 / L) ≤ (44 - L) * 1 :=
        mul_le_mul_of_nonneg_left h8L (by linarith)
      linarith
    have hpsi : L - 8 * Real.log L ≤ 44 - 8 * Real.log 44 := by linarith
    have h6 : 6 * Real.log 10 + 8 * Real.log 44 < 44 := by linarith
    have hlog : Real.log ((10 : ℝ) ^ 6 * 44 ^ 8) < 44 := by
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow (10 : ℝ) 6,
        Real.log_pow (44 : ℝ) 8]
      push_cast
      linarith
    have hlt : (10 : ℝ) ^ 6 * 44 ^ 8 < Real.exp 44 :=
      (Real.log_lt_log_iff (by positivity) (Real.exp_pos 44)).mp (by rw [Real.log_exp]; exact hlog)
    linarith [exp_44_le_10pow6_mul_44pow8]

end Work.Deep.Sparse
