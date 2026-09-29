import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.log_two_bounds
import Submission.Work.Cert.expTaylor_le_exp

/-! # Soundness of the integer lower bound `expLo` of `S · exp(x/S)`

`Work.Cert.expLo` (see `Submission/Work/Cert/Defs.lean`) is the integer routine used by the leaf
checker `leafOK` to certify `log |h(q')| ≤ G/S`: it must be a *lower* bound for `S · exp(x/S)`.

The argument, case by case (`S = 2^40·10^8`, `LN2LO < S·log 2 < LN2HI`, see `log_two_bounds`):

* `0 ≤ x`: `k = ⌊x/LN2HI⌋ ≥ 0` and `y = x - k·LN2HI ∈ [0, LN2HI)` satisfy `x = y + k·LN2HI`.
  The truncated, floored Taylor sum `expTaylor y 14 1 S S` is at most `S·exp(y/S)`
  (`expTaylor_le_exp`), and `2^k ≤ exp(k·LN2HI/S)` because `log 2 ≤ LN2HI/S`.  Hence
  `expTaylor(y)·2^k ≤ S·exp(y/S)·exp(k·LN2HI/S) = S·exp(x/S)`.

* `x < 0`: with `q = ⌊(-x)/LN2LO⌋ ≥ 0` and `k = -q-1 < 0`, `y = x - k·LN2LO ∈ [0, LN2LO)` again
  satisfies `x = y + k·LN2LO`.  Now `2^k ≤ exp(k·LN2LO/S)` because `log 2 ≥ LN2LO/S` (and `k ≤ 0`),
  and `⌊expTaylor(y)/2^{-k}⌋ ≤ expTaylor(y)·2^k` since `expTaylor y ≥ 0` (with `y ≥ 0`).

Everything else is the rounding fact that `Int.ediv` by a positive divisor is a real lower bound
for the quotient. -/

namespace Work.Cert

open Complex Submission.CDTPlan

namespace ExpLoAux

lemma two_pow_pos (n : ℕ) : (0 : ℤ) < two_pow n := by
  show (0 : ℤ) < ((2 ^ n : ℕ) : ℤ)
  exact_mod_cast Nat.pow_pos (by norm_num : (0 : ℕ) < 2)

/-- the certified integer power `two_pow` casts to the real power `2^k` (for `k ≥ 0`). -/
lemma two_pow_int_cast (k : ℤ) (hk : 0 ≤ k) : ((two_pow k.toNat : ℤ) : ℝ) = (2 : ℝ) ^ k := by
  have h1 : ((two_pow k.toNat : ℤ) : ℝ) = (2 : ℝ) ^ (k.toNat) := by
    rw [two_pow]; norm_num
  rw [h1, ← zpow_natCast, Int.toNat_of_nonneg hk]

/-- `Int.ediv` by a positive divisor is a lower bound of the real quotient. -/
lemma ediv_le_div (a : ℤ) {b : ℤ} (hb : 0 < b) :
    ((Int.ediv a b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  exact_mod_cast Int.ediv_mul_le a hb.ne'

/-- `2^k = exp(k · log 2)` for every integer `k`. -/
lemma two_zpow_eq_exp (k : ℤ) : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
  rw [← Real.rpow_intCast (2 : ℝ) k, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- `2^k ≤ exp(k·LN2HI/S)` for `k ≥ 0`, since `log 2 ≤ LN2HI/S`. -/
lemma two_pow_le_exp_hi (k : ℤ) (hk : 0 ≤ k) :
    (2 : ℝ) ^ k ≤ Real.exp ((k : ℝ) * (LN2HI : ℝ) / (S : ℝ)) := by
  rw [two_zpow_eq_exp]
  apply Real.exp_le_exp.mpr
  have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  calc (k : ℝ) * Real.log 2 ≤ (k : ℝ) * ((LN2HI : ℝ) / (S : ℝ)) :=
        mul_le_mul_of_nonneg_left log_two_bounds.2 hk'
    _ = (k : ℝ) * (LN2HI : ℝ) / (S : ℝ) := by ring

/-- `2^k ≤ exp(k·LN2LO/S)` for `k ≤ 0`, since `LN2LO/S ≤ log 2`. -/
lemma two_pow_le_exp_lo (k : ℤ) (hk : k ≤ 0) :
    (2 : ℝ) ^ k ≤ Real.exp ((k : ℝ) * (LN2LO : ℝ) / (S : ℝ)) := by
  rw [two_zpow_eq_exp]
  apply Real.exp_le_exp.mpr
  have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
  calc (k : ℝ) * Real.log 2 ≤ (k : ℝ) * ((LN2LO : ℝ) / (S : ℝ)) :=
        mul_le_mul_of_nonpos_left log_two_bounds.1 hk'
    _ = (k : ℝ) * (LN2LO : ℝ) / (S : ℝ) := by ring

lemma expLo_nonneg (x : ℤ) (hx : 0 ≤ x) :
    (expLo x : ℝ) ≤ (S : ℝ) * Real.exp ((x : ℝ) / (S : ℝ)) := by
  have hSr : (0 : ℝ) < (S : ℝ) := by rw [S]; norm_num
  rw [expLo, if_pos hx]
  dsimp only
  push_cast
  set k : ℤ := fdiv x LN2HI with hk
  set y : ℤ := x - k * LN2HI with hy
  have hLN : (0 : ℤ) < LN2HI := by rw [LN2HI]; norm_num
  have hk0 : 0 ≤ k := by rw [hk]; exact Int.ediv_nonneg hx hLN.le
  have hy0 : 0 ≤ y := by
    rw [hy, hk, fdiv]
    exact sub_nonneg.mpr (Int.ediv_mul_le x hLN.ne')
  have hyx : ((y : ℝ) + (k : ℝ) * (LN2HI : ℝ)) / (S : ℝ) = (x : ℝ) / (S : ℝ) := by
    congr 1
    rw [hy]; push_cast; ring
  have hpk : (0 : ℝ) ≤ (2 : ℝ) ^ k := le_of_lt (zpow_pos (by norm_num) k)
  calc ((expTaylor y 14 1 S S : ℤ) : ℝ) * ((two_pow k.toNat : ℤ) : ℝ)
      = (expTaylor y 14 1 S S : ℝ) * (2 : ℝ) ^ k := by rw [two_pow_int_cast k hk0]
    _ ≤ ((S : ℝ) * Real.exp ((y : ℝ) / (S : ℝ))) * (2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (expTaylor_le_exp y hy0 14) hpk
    _ ≤ ((S : ℝ) * Real.exp ((y : ℝ) / (S : ℝ))) * Real.exp ((k : ℝ) * (LN2HI : ℝ) / (S : ℝ)) :=
        mul_le_mul_of_nonneg_left (two_pow_le_exp_hi k hk0)
          (le_of_lt (mul_pos hSr (Real.exp_pos _)))
    _ = (S : ℝ) * Real.exp ((x : ℝ) / (S : ℝ)) := by
        rw [mul_assoc, ← Real.exp_add, ← add_div, hyx]

lemma expLo_neg (x : ℤ) (hx : ¬ 0 ≤ x) :
    (expLo x : ℝ) ≤ (S : ℝ) * Real.exp ((x : ℝ) / (S : ℝ)) := by
  have hSr : (0 : ℝ) < (S : ℝ) := by rw [S]; norm_num
  have hLN2LO : (0 : ℤ) < LN2LO := by rw [LN2LO]; norm_num
  rw [expLo, if_neg hx]
  dsimp only
  rw [fdiv]
  set q : ℤ := (-x) / LN2LO with hq
  set k : ℤ := -q - 1 with hk
  set y : ℤ := x - k * LN2LO with hy
  have hq0 : 0 ≤ q := by rw [hq]; exact Int.ediv_nonneg (by omega) hLN2LO.le
  have hk0 : k ≤ 0 := by rw [hk]; omega
  have hmk0 : 0 ≤ -k := by omega
  have hy0 : 0 ≤ y := by
    have h := Int.lt_ediv_add_one_mul_self (-x) hLN2LO
    rw [hy, hk, hq]
    linarith
  have hyx : ((y : ℝ) + (k : ℝ) * (LN2LO : ℝ)) / (S : ℝ) = (x : ℝ) / (S : ℝ) := by
    congr 1
    rw [hy]; push_cast; ring
  have hpk : (0 : ℝ) ≤ (2 : ℝ) ^ k := le_of_lt (zpow_pos (by norm_num) k)
  calc ((Int.ediv (expTaylor y 14 1 S S) (two_pow (-k).toNat) : ℤ) : ℝ)
      ≤ (expTaylor y 14 1 S S : ℝ) / ((two_pow (-k).toNat : ℤ) : ℝ) :=
        ediv_le_div _ (two_pow_pos _)
    _ = (expTaylor y 14 1 S S : ℝ) * (2 : ℝ) ^ k := by
        rw [two_pow_int_cast (-k) hmk0, zpow_neg, div_inv_eq_mul]
    _ ≤ ((S : ℝ) * Real.exp ((y : ℝ) / (S : ℝ))) * (2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (expTaylor_le_exp y hy0 14) hpk
    _ ≤ ((S : ℝ) * Real.exp ((y : ℝ) / (S : ℝ))) * Real.exp ((k : ℝ) * (LN2LO : ℝ) / (S : ℝ)) :=
        mul_le_mul_of_nonneg_left (two_pow_le_exp_lo k hk0)
          (le_of_lt (mul_pos hSr (Real.exp_pos _)))
    _ = (S : ℝ) * Real.exp ((x : ℝ) / (S : ℝ)) := by
        rw [mul_assoc, ← Real.exp_add, ← add_div, hyx]

end ExpLoAux

theorem expLo_sound : ExpLoSound := by
  intro x
  by_cases hx : 0 ≤ x
  · exact ExpLoAux.expLo_nonneg x hx
  · exact ExpLoAux.expLo_neg x hx

end Work.Cert
