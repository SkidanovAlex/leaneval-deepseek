import Mathlib
import Submission.Work.Haupt.qp_defs

/-!
# Helpers for the semi-finite split `∑_{n ∈ ℤ} sfTerm = Afun + Bfun`

This file collects the elementary rewriting lemmas about `sfTerm`, `qhalfInt`, `qpInt`
that are used both in `Work.Haupt.semifinite_split` and in the auxiliary lemmas
`Work.Haupt.neg_part_tsum` and `Work.Haupt.sf_summable_nat`.
-/

open scoped BigOperators

namespace Work.Haupt

/-- For `k < j` we have `q ^ j * q ^ (-(k : ℤ)) = q ^ (j - k)`; the strict inequality
makes the formula valid also for `q = 0`. -/
lemma zpow_mul_zpow_neg {q : ℂ} {j : ℤ} {k : ℕ} (hk : (k : ℤ) < j) :
    q ^ j * q ^ (-(k : ℤ)) = q ^ (j - (k : ℤ)) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · have hj : j ≠ 0 := by omega
    have hjk : j - (k : ℤ) ≠ 0 := by omega
    rw [zero_zpow _ hj, zero_zpow _ hjk, zero_mul]
  · rw [← zpow_add₀ hq0, ← sub_eq_add_neg]

/-- For `q ≠ 0` the same identity holds without a restriction on `k`. -/
lemma zpow_mul_zpow_neg_of_ne {q : ℂ} (hq0 : q ≠ 0) (a : ℤ) (k : ℕ) :
    q ^ a * q ^ (-(k : ℤ)) = q ^ (a - (k : ℤ)) := by
  rw [← zpow_add₀ hq0, ← sub_eq_add_neg]

/-- The `n ≥ 0` part of the semi-finite summand. -/
lemma sfTerm_natCast (q z : ℂ) (m n : ℕ) :
    sfTerm q z m (n : ℤ) = qhalf q n * z ^ n / qpNat (q ^ ((m : ℤ) + 1)) q n := by
  simp [sfTerm, qhalfInt_natCast, qpInt_ofNat, zpow_natCast]

/-- The `n = -k ≤ 0` part of the semi-finite summand, before the reciprocity for `qpInt`. -/
lemma sfTerm_neg_natCast (q z : ℂ) (m k : ℕ) :
    sfTerm q z m (-(k : ℤ)) =
      qhalf q (k + 1) * z ^ (-(k : ℤ)) / qpInt (q ^ ((m : ℤ) + 1)) q (-(k : ℤ)) := by
  simp [sfTerm, qhalfInt_neg_natCast]

/-- Reciprocity of `qpInt` for `0 ≤ k ≤ m`. -/
lemma qpInt_neg_eq {q : ℂ} {m k : ℕ} (hk : k ≤ m) :
    qpInt (q ^ ((m : ℤ) + 1)) q (-(k : ℤ)) =
      (qpNat (q ^ ((m : ℤ) + 1 - (k : ℤ))) q k)⁻¹ := by
  rw [qpInt_neg_natCast, zpow_mul_zpow_neg (by omega : ((k : ℤ)) < (m : ℤ) + 1)]

/-- The explicit value of the `n = -k` term for `k ≤ m`, as it appears in `Bfun`. -/
lemma sfTerm_neg_eq {q z : ℂ} {m k : ℕ} (hk : k ≤ m) :
    sfTerm q z m (-(k : ℤ)) =
      qpNat (q ^ ((m : ℤ) + 1 - (k : ℤ))) q k * qhalf q (k + 1) * z ^ (-(k : ℤ)) := by
  rw [sfTerm_neg_natCast, qpInt_neg_eq hk, div_inv_eq_mul]
  ring

/-- For `k ≥ m + 1` the `qpNat` factor in `qpInt (q ^ (m+1)) q (-k)` vanishes. -/
lemma qpNat_shift_eq_zero {q : ℂ} (hq0 : q ≠ 0) {m k : ℕ} (hk : m + 1 ≤ k) :
    qpNat (q ^ ((m : ℤ) + 1 - (k : ℤ))) q k = 0 := by
  refine Finset.prod_eq_zero (i := k - 1 - m) (Finset.mem_range.mpr (by omega)) ?_
  have hcast : ((k - 1 - m : ℕ) : ℤ) = (k : ℤ) - 1 - (m : ℤ) := by
    rw [Nat.cast_sub (show m ≤ k - 1 by omega), Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  have hexp : (m : ℤ) + 1 - (k : ℤ) + ((k - 1 - m : ℕ) : ℤ) = 0 := by
    rw [hcast]; ring
  rw [← zpow_natCast q (k - 1 - m), ← zpow_add₀ hq0, hexp, zpow_zero, sub_self]

/-- All terms of the semi-finite sum with index `n ≤ -(m+1)` vanish. -/
lemma sfTerm_neg_eq_zero {q z : ℂ} (hq : ‖q‖ < 1) {m k : ℕ} (hk : m + 1 ≤ k) :
    sfTerm q z m (-(k : ℤ)) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [sfTerm_neg_natCast]
    have h1 : (1 : ℕ) ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have hz0 : qhalf (0 : ℂ) (k + 1) = 0 := by
      simp only [qhalf]
      exact Finset.prod_eq_zero h1 (by simp)
    rw [hz0, zero_mul, zero_div]
  · have h0 : qpInt (q ^ ((m : ℤ) + 1)) q (-(k : ℤ)) = 0 := by
      rw [qpInt_neg_natCast, zpow_mul_zpow_neg_of_ne hq0]
      rw [qpNat_shift_eq_zero hq0 hk, inv_zero]
    rw [sfTerm_neg_natCast, h0, div_zero]

end Work.Haupt
