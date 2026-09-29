import Mathlib
import Submission.Work.Haupt.qp_defs
import Submission.Work.Haupt.sf_helpers
import Submission.Work.Haupt.sf_aux

/-!
# The semi-finite `q`-series identity at `q = 0`

The general semi-finite identity (`Work.Haupt.semifinite`)

  `∑_{n ∈ ℤ} q^{n(n-1)/2} z^n / (q^{m+1};q)_n = (q;q)_m (-q/z;q)_m (-z;q)_∞`

degenerates at `q = 0` to the elementary statement `1 + z = 1 + z`: all summands with
`n < 0` or `n ≥ 2` vanish because of the `q^{n(n-1)/2}` factor, leaving the two terms
`n = 0, 1`.  This file records this degenerate case explicitly; it is the input
`q = 0` used in the limiting argument for the Jacobi triple product.
-/

open scoped BigOperators

set_option linter.unusedVariables false

namespace Work.Haupt

/-- `(-z; 0)_∞ = 1 + z`: at `q = 0` every factor with `n ≥ 1` equals `1`. -/
lemma qpInf_zero_neg (z : ℂ) : qpInf (-z) 0 = 1 + z := by
  rw [qpInf, tprod_eq_prod (s := {0})]
  · simp
  · intro b hb
    simp at hb
    rw [zero_pow hb]
    ring

/-- `qhalf 0 k = 0` for `k ≥ 2`, since the factor `0 ^ 1` occurs. -/
lemma qhalf_zero_of_two_le (k : ℕ) (hk : 2 ≤ k) : qhalf (0:ℂ) k = 0 := by
  rw [qhalf]
  exact Finset.prod_eq_zero (i := 1) (Finset.mem_range.mpr (by omega)) (by simp)

/-- The non-negative part of `sfTerm` vanishes for `n ≥ 2` at `q = 0`. -/
lemma sfTerm_zero_nat (z : ℂ) (m k : ℕ) (hk : 2 ≤ k) : sfTerm 0 z m (k:ℤ) = 0 := by
  rw [sfTerm_natCast]
  rw [qhalf_zero_of_two_le k hk, zero_mul, zero_div]

/-- The negative part of `sfTerm` vanishes for `n ≤ -1` at `q = 0`. -/
lemma sfTerm_zero_neg (z : ℂ) (m k : ℕ) (hk : 1 ≤ k) : sfTerm 0 z m (-(k:ℤ)) = 0 := by
  by_cases hkm : k ≤ m
  · rw [sfTerm_neg_eq hkm, qhalf_zero_of_two_le (k+1) (by omega), mul_zero, zero_mul]
  · rw [sfTerm_neg_eq_zero (by norm_num : ‖(0:ℂ)‖ < 1) (by omega)]

/-- The summand at `n = 1` is `z` when `q = 0`. -/
lemma sfTerm_zero_one (z : ℂ) (m : ℕ) : sfTerm 0 z m 1 = z := by
  simp only [sfTerm, qhalfInt_one, zpow_one]
  have hq : qpInt (0 ^ ((m:ℤ)+1)) (0:ℂ) (1:ℤ) = 1 := by
    show qpNat (0 ^ ((m:ℤ)+1)) (0:ℂ) 1 = 1
    rw [qpNat_one, zero_zpow ((m:ℤ)+1) (by omega), sub_zero]
  rw [hq, div_one, one_mul]

/-- At `q = 0` the semi-finite sum reduces to its two surviving terms `1 + z`. -/
theorem semifinite_zero (z : ℂ) (hz : z ≠ 0) (m : ℕ) :
    (∑' n : ℤ, sfTerm 0 z m n) = qpNat 0 0 m * qpNat (-0/z) 0 m * qpInf (-z) 0 := by
  have hsupp : ∀ n : ℤ, n ∉ ({0, 1} : Finset ℤ) → sfTerm 0 z m n = 0 := by
    intro n hn
    obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
    · rw [hk] at hn ⊢
      have h0 : k ≠ 0 := fun h => hn (by simp [h])
      have h1 : k ≠ 1 := fun h => hn (by simp [h])
      exact sfTerm_zero_nat z m k (by omega)
    · rw [hk] at hn ⊢
      have h0 : k ≠ 0 := fun h => hn (by simp [h])
      exact sfTerm_zero_neg z m k (by omega)
  rw [tsum_eq_sum hsupp]
  have h0 : sfTerm 0 z m 0 = 1 := by simp [sfTerm]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton, h0, sfTerm_zero_one]
  rw [qpInf_zero_neg]
  simp [qpNat]

end Work.Haupt
