import Mathlib
import Submission.Work.Fx.FxCommon

/-!
# Fixed-point computation of `log 2`: the numerical layer (definitions)

The library word `Work.Fx.logTwoWord` computes an integer `u` with `|u - 2^p log 2| ≤ 1`.

* `Real.log 2 = Σ_{n ≥ 1} 1/(n 2^n)`  (the Mercator series at `x = 1/2`),
* the program sums `logA p n = ⌊2^P / (2^n · n)⌋` for `n = 1, …, logM p` at the internal scale
  `2^P` with `P = logP p = 2p+21 = p + logG p + 1`,
* each new summand is obtained from the previous one by one division by `2` (the current
  `logD p i = ⌊2^P/2^i⌋`) and one division by the counter `i+1` (`hi.tdiv`),
* finally the accumulator is rounded to precision `p`: `logU p = (S + 2^logG p)/2^(logG p+1)`.

Everything is exact integer arithmetic; the only rounding is the `⌊·⌋` in `logD` and `logA`
(bounded by `1` per term) and the final rounding (bounded by `1/2`).
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- Internal scale exponent `P = 2p+21`. -/
def logP (p : ℕ) : ℕ := 2 * p + 21

/-- Guard exponent `G = p+20`. -/
def logG (p : ℕ) : ℕ := p + 20

/-- Number of the last loop index: the loop runs `i = 0, …, logM p`. -/
def logM (p : ℕ) : ℕ := 2 * p + 21

/-- `⌊2^(logP p)/2^i⌋`. -/
def logD (p i : ℕ) : ℕ := 2 ^ logP p / 2 ^ i

/-- The `n`-th summand `⌊2^logP p/(2^n · n)⌋`. -/
def logA (p n : ℕ) : ℕ := logD p n / n

/-- Partial sum `logS p k = Σ_{n=1}^{k} logA p n`. -/
def logS (p k : ℕ) : ℕ := ∑ j ∈ Finset.range k, logA p (j + 1)

/-- The final integer approximation of `2^p log 2`. -/
def logU (p : ℕ) : ℕ := (logS p (logM p + 1) + 2 ^ logG p) / 2 ^ (logG p + 1)

/-- Uniform bound on the size `isz` of every value occurring in the loop. -/
def logSZ (p : ℕ) : ℕ := 2 * p + 24

theorem logP_eq (p : ℕ) : logP p = p + logG p + 1 := by
  unfold logP logG; ring

theorem logG_add_one (p : ℕ) : logG p + 1 = p + 21 := by
  unfold logG; ring

theorem logP_eq_logM (p : ℕ) : logP p = logM p := rfl

theorem logD_zero (p : ℕ) : logD p 0 = 2 ^ logP p := by
  simp [logD]

theorem logD_succ (p i : ℕ) : logD p (i + 1) = logD p i / 2 := by
  simp only [logD, pow_succ]
  rw [Nat.div_div_eq_div_mul]

theorem logD_le_pow (p i : ℕ) : logD p i ≤ 2 ^ logP p :=
  Nat.div_le_self _ _

theorem logA_le_logD (p n : ℕ) : logA p n ≤ logD p n :=
  Nat.div_le_self _ _

theorem logS_zero (p : ℕ) : logS p 0 = 0 := by
  simp [logS]

theorem logS_succ (p k : ℕ) : logS p (k + 1) = logS p k + logA p (k + 1) := by
  simp only [logS, Finset.sum_range_succ]

theorem logD_eq_pow (p : ℕ) {i : ℕ} (hi : i ≤ logP p) : logD p i = 2 ^ (logP p - i) := by
  simp only [logD]
  exact Nat.pow_div hi (by norm_num)

theorem logM_eq (p : ℕ) : logM p = 2 * p + 21 := rfl

/-! ## Casts of the `ℕ`-definitions to the `ℤ` values used by the machine -/

theorem cast_tdiv (m n : ℕ) : ((m / n : ℕ) : ℤ) = (m : ℤ).tdiv (n : ℤ) := Int.ofNat_tdiv m n

theorem cast_fdiv (m n : ℕ) : ((m / n : ℕ) : ℤ) = (m : ℤ).fdiv (n : ℤ) := Int.ofNat_fdiv m n

theorem logD_succ_Z (p i : ℕ) : ((logD p (i + 1) : ℕ) : ℤ) = ((logD p i : ℕ) : ℤ).tdiv 2 := by
  rw [logD_succ]; exact cast_tdiv _ 2

theorem logA_cast (p n : ℕ) : ((logA p n : ℕ) : ℤ) = ((logD p n : ℕ) : ℤ).tdiv (n : ℤ) := by
  rw [logA]; exact cast_tdiv _ n

theorem logS_succ_Z (p i : ℕ) :
    ((logS p (i + 1) : ℕ) : ℤ) = ((logS p i : ℕ) : ℤ) + ((logA p (i + 1) : ℕ) : ℤ) := by
  rw [logS_succ]; push_cast; ring

theorem logU_cast (p : ℕ) :
    ((logU p : ℕ) : ℤ) =
      (((logS p (logM p + 1) : ℕ) : ℤ) + (2 : ℤ) ^ (p + 20)).fdiv ((2 : ℤ) ^ (p + 21)) := by
  unfold logU logG
  rw [cast_fdiv]
  push_cast
  ring_nf

theorem logSZ_eq (p : ℕ) : logSZ p = 2 * p + 24 := rfl

theorem isz_natCast (n : ℕ) : isz ((n : ℤ)) = n.size + 2 := by
  simp [isz, Int.natAbs_natCast]

theorem isz_natCast_le_self (n : ℕ) : isz ((n : ℤ)) ≤ n + 2 := by
  rw [isz_natCast]
  have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  omega

end Work.Fx
