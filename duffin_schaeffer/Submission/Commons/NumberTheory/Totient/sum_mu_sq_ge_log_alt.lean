import Mathlib
import Submission.Commons.NumberTheory.Totient.totient_sum_sub_harmonic_ge_of_large
import Submission.Commons.NumberTheory.Totient.totient_sum_sub_harmonic_ge_of_small

/-!
# `∑_{r ≤ z} μ(r)²/φ(r) ≥ log z + 1`

We prove the elementary lower bound
`Real.log z + 1 ≤ ∑_{r ≤ z} μ(r)²/φ(r)` for every `z ≥ 1`.

**Strategy.**  Let `H_z = harmonic z` be the `z`-th harmonic number and
`S(z) = ∑_{r ≤ z} μ(r)²/φ(r)`.  Writing `E(z) = S(z) - H_z`:

* `Real.log z < H_z - 11/20`, because `H_z - Real.log z = eulerMascheroniSeq' z > γ > 11/20`
  (Mathlib's Euler–Mascheroni machinery plus an explicit Taylor bound on `log 21`);
* `E(z) ≥ 9/20` for every `z ≥ 2` with `z ≠ 4` — this is split into two commons lemmas
  (`totient_sum_sub_harmonic_ge_of_small` for `z ≤ 1000` and
  `totient_sum_sub_harmonic_ge_of_large` for `z ≥ 1001`), each proved by an explicit
  Euler-product / harmonic-difference argument.

Combining, `S(z) ≥ H_z + 9/20 > log z + 11/20 + 9/20 = log z + 1`.
The two exceptional values `z = 1` (`S = 1`) and `z = 4` (`S = 5/2 > log 4 + 1`)
are checked directly.
-/

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.Totient

/-- `γ > 11/20`, from Mathlib's `eulerMascheroniSeq 20 = H_20 - log 21` together with
the explicit bound `log 21 < 3.047` (obtained from the Taylor expansion of `exp`). -/
lemma gamma_gt_11_20 : (11/20 : ℝ) < Real.eulerMascheroniConstant := by
  refine lt_trans ?_ (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 20)
  rw [Real.eulerMascheroniSeq]
  have h : Real.log 21 < (3.047 : ℝ) := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 21)]
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3.047) 11
    have hval : (21:ℝ) < ∑ k ∈ Finset.range 11, (3.047:ℝ)^k / k.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith
  have hH : (harmonic 20 : ℝ) > 11/20 + 3.047 := by
    rw [harmonic]; push_cast; norm_num
  linarith

/-- `Real.log z < H_z - 11/20` for `z ≥ 1`. -/
lemma harmonic_sub_log_gt (z : ℕ) (hz : 1 ≤ z) :
    Real.log (z : ℝ) < (harmonic z : ℝ) - 11/20 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' z
  rw [Real.eulerMascheroniSeq'] at h
  rw [if_neg (by omega : z ≠ 0)] at h
  linarith [gamma_gt_11_20]

/-- The totient sum evaluated at `z = 1` equals `1`. -/
private lemma sum_one : (∑ r ∈ Finset.Icc 1 1,
    ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ)) = 1 := by
  set g : ℕ → ℝ := fun r => ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ)
    with hg
  have h1 : (∑ r ∈ Finset.Icc 1 1, g r) = g 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton]
  rw [h1]
  simp only [g, ArithmeticFunction.moebius_apply_one, Nat.totient_one]
  norm_num

/-- The totient sum evaluated at `z = 4` equals `5/2`. -/
private lemma sum_four : (∑ r ∈ Finset.Icc 1 4,
    ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ)) = 5/2 := by
  set g : ℕ → ℝ := fun r => ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ)
    with hg
  have h4 : (∑ r ∈ Finset.Icc 1 4, g r) = (∑ r ∈ Finset.Icc 1 3, g r) + g 4 :=
    Finset.sum_Icc_succ_top (a:=1) (b:=3) (by norm_num) g
  have h3 : (∑ r ∈ Finset.Icc 1 3, g r) = (∑ r ∈ Finset.Icc 1 2, g r) + g 3 :=
    Finset.sum_Icc_succ_top (a:=1) (b:=2) (by norm_num) g
  have h2 : (∑ r ∈ Finset.Icc 1 2, g r) = (∑ r ∈ Finset.Icc 1 1, g r) + g 2 :=
    Finset.sum_Icc_succ_top (a:=1) (b:=1) (by norm_num) g
  have h1 : (∑ r ∈ Finset.Icc 1 1, g r) = g 1 := by rw [Finset.Icc_self, Finset.sum_singleton]
  rw [h4, h3, h2, h1]
  have e1 : g 1 = 1 := by
    simp only [g, ArithmeticFunction.moebius_apply_one, Nat.totient_one]; norm_num
  have e2 : g 2 = 1 := by
    simp only [g, ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
      Nat.totient_prime (by norm_num : Nat.Prime 2)]; norm_num
  have e3 : g 3 = 1/2 := by
    simp only [g, ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
      Nat.totient_prime (by norm_num : Nat.Prime 3)]; norm_num
  have e4 : g 4 = 0 := by
    have h : (4:ℕ) = 2^2 := by norm_num
    simp only [g, h, ArithmeticFunction.moebius_apply_prime_pow (by norm_num : Nat.Prime 2)
      (by norm_num : (2:ℕ) ≠ 0)]
    norm_num
  rw [e1, e2, e3, e4]; norm_num

/-- **Main theorem.**  `Real.log z + 1 ≤ ∑_{r ≤ z} μ(r)²/φ(r)`. -/
theorem sum_mu_sq_ge_log_alt (z : ℕ) (hz : 1 ≤ z) :
    Real.log (z : ℝ) + 1 ≤ ∑ r ∈ Finset.Icc 1 z,
      ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
  rcases eq_or_lt_of_le hz with h1 | h2
  · -- z = 1
    subst h1
    rw [sum_one]
    simp only [Nat.cast_one, Real.log_one]
    norm_num
  · -- 1 < z
    by_cases h4 : z = 4
    · -- z = 4
      subst h4
      rw [sum_four]
      have hlog4 : Real.log (4:ℝ) < 3/2 := by
        have h := Real.log_two_lt_d9
        rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith
      linarith
    · -- 2 ≤ z, z ≠ 4
      have hE : (9/20 : ℝ) ≤ (∑ r ∈ Finset.Icc 1 z,
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ))
          - (harmonic z : ℝ) := by
        by_cases hle : z ≤ 1000
        · exact totient_sum_sub_harmonic_ge_of_small z (by omega) hle h4
        · rw [not_le] at hle
          exact totient_sum_sub_harmonic_ge_of_large z (by omega)
      have hlog := harmonic_sub_log_gt z hz
      linarith

end Commons.NumberTheory.Totient
