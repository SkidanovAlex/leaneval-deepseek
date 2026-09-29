import Mathlib
import Submission.Work.Haupt.jtp_defs

/-!
# Euler's pentagonal-number form of the theta series at `(X^3, -X)`

For `‖X‖ < 1` we have
`jtpTheta (X^3) (-X) = ∑_{k ≥ 0} (-1)^k (X^{3k²+k} - X^{3k²+5k+2})`.

This is the splitting of the two-sided theta series `∑_{n ∈ ℤ} (X^3)^{n²} (-X)^n`
according to the sign of `n`: for `n ≥ 0` the terms are `(-1)^n X^{3n²+n}`, and for
`n = -(k+1)` they are `(-1)^{k+1} X^{3(k+1)²-(k+1)} = (-1)^{k+1} X^{3k²+5k+2}`
(since `3(k+1)² - (k+1) = 3k²+5k+2`). No triple product is needed.
-/

namespace Work.Haupt

open scoped BigOperators

/-- The `n`-th term with `n ≥ 0`. -/
private lemma jtp_pos_term (X : ℂ) (n : ℕ) :
    (X ^ 3) ^ ((n : ℤ) ^ 2) * (-X) ^ ((n : ℤ)) = (-1) ^ n * X ^ (3 * n ^ 2 + n) := by
  have h1 : ((n : ℤ)) ^ 2 = ((n ^ 2 : ℕ) : ℤ) := by push_cast; ring
  have h2 : (X ^ 3) ^ ((n : ℤ) ^ 2) = X ^ (3 * n ^ 2) := by
    rw [h1, zpow_natCast, ← pow_mul X 3 (n ^ 2)]
  have h3 : (-X) ^ ((n : ℤ)) = (-1) ^ n * X ^ n := by
    rw [zpow_natCast, neg_eq_neg_one_mul X, mul_pow]
  rw [h2, h3]
  calc X ^ (3 * n ^ 2) * ((-1) ^ n * X ^ n)
      = (-1) ^ n * (X ^ (3 * n ^ 2) * X ^ n) := by
        rw [← mul_assoc, mul_comm (X ^ (3 * n ^ 2)) ((-1) ^ n), mul_assoc]
    _ = (-1) ^ n * X ^ (3 * n ^ 2 + n) := by rw [pow_add]

/-- `(X^3)^m = X^(3m)`, with `X^3` the natural-number power and `m : ℤ`. -/
private lemma pow_three_zpow (X : ℂ) (m : ℤ) : (X ^ 3) ^ m = X ^ (3 * m) := by
  have h : (X : ℂ) ^ (3 : ℕ) = X ^ (3 : ℤ) := (zpow_natCast X 3).symm
  rw [h, ← zpow_mul X (3 : ℤ) m]

/-- `(-X)^m = (-1)^m * X^m` for integer `m`. -/
private lemma neg_zpow' (X : ℂ) (m : ℤ) : (-X) ^ m = (-1) ^ m * X ^ m := by
  rw [show (-X : ℂ) = -1 * X by ring, mul_zpow]

/-- The term with `n = -(k+1) < 0`. -/
private lemma jtp_neg_term (X : ℂ) (hX0 : X ≠ 0) (n : ℕ) :
    (X ^ 3) ^ ((-((n : ℤ) + 1)) ^ 2) * (-X) ^ (-((n : ℤ) + 1))
      = -((-1) ^ n * X ^ (3 * n ^ 2 + 5 * n + 2)) := by
  have hsign : (-1 : ℂ) ^ (-((n : ℤ) + 1)) = -((-1) ^ n) := by
    have h : -((n : ℤ) + 1) = -(((n + 1 : ℕ) : ℤ)) := by push_cast; ring
    rw [h, zpow_neg, zpow_natCast, ← inv_pow, show ((-1 : ℂ))⁻¹ = -1 by simp,
      pow_succ, mul_neg, mul_one]
  have hexp : 3 * ((-((n : ℤ) + 1)) ^ 2) + (-((n : ℤ) + 1))
      = ((3 * n ^ 2 + 5 * n + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [pow_three_zpow X ((-((n : ℤ) + 1)) ^ 2), neg_zpow' X (-((n : ℤ) + 1))]
  calc X ^ (3 * ((-((n : ℤ) + 1)) ^ 2))
        * ((-1) ^ (-((n : ℤ) + 1)) * X ^ (-((n : ℤ) + 1)))
      = (-1) ^ (-((n : ℤ) + 1))
          * (X ^ (3 * ((-((n : ℤ) + 1)) ^ 2)) * X ^ (-((n : ℤ) + 1))) := by
        rw [← mul_assoc,
          mul_comm (X ^ (3 * ((-((n : ℤ) + 1)) ^ 2))) ((-1) ^ (-((n : ℤ) + 1))),
          mul_assoc]
    _ = (-1) ^ (-((n : ℤ) + 1))
          * X ^ (3 * ((-((n : ℤ) + 1)) ^ 2) + (-((n : ℤ) + 1))) := by
        rw [zpow_add₀ hX0]
    _ = -((-1) ^ n * X ^ (3 * n ^ 2 + 5 * n + 2)) := by
        rw [hexp, zpow_natCast, hsign, neg_mul]

private lemma le_three_sq_add (n : ℕ) : n ≤ 3 * n ^ 2 + n :=
  Nat.le_add_left n (3 * n ^ 2)

private lemma le_three_sq_add_five (n : ℕ) : n ≤ 3 * n ^ 2 + 5 * n + 2 := by
  have h : (0 : ℕ) ≤ 3 * n ^ 2 := Nat.zero_le _
  omega

theorem jtpTheta_eq_pentagonal (X : ℂ) (hX : ‖X‖ < 1) :
    jtpTheta (X ^ 3) (-X)
      = ∑' k : ℕ, (-1) ^ k * (X ^ (3 * k ^ 2 + k) - X ^ (3 * k ^ 2 + 5 * k + 2)) := by
  have hA : Summable (fun n : ℕ => (-1 : ℂ) ^ n * X ^ (3 * n ^ 2 + n)) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => ‖X‖ ^ n)
    · rw [summable_geometric_iff_norm_lt_one]; simpa using hX
    · intro n
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact pow_le_pow_of_le_one (norm_nonneg X) (le_of_lt hX) (le_three_sq_add n)
  have hB : Summable (fun n : ℕ => (-1 : ℂ) ^ n * X ^ (3 * n ^ 2 + 5 * n + 2)) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => ‖X‖ ^ n)
    · rw [summable_geometric_iff_norm_lt_one]; simpa using hX
    · intro n
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact pow_le_pow_of_le_one (norm_nonneg X) (le_of_lt hX) (le_three_sq_add_five n)
  by_cases hX0 : X = 0
  · subst hX0
    rw [jtpTheta]
    have hL : (∑' n : ℤ, ((0 : ℂ) ^ 3) ^ (n ^ 2) * (-(0 : ℂ)) ^ n) = 1 := by
      rw [tsum_eq_single (0 : ℤ) (fun n hn => by
        have h3 : ((0 : ℂ) ^ 3) = 0 := by norm_num
        rw [h3, zero_zpow (n ^ 2) (pow_ne_zero 2 hn), zero_mul])]
      simp
    have hR : (∑' k : ℕ, (-1 : ℂ) ^ k
        * ((0 : ℂ) ^ (3 * k ^ 2 + k) - (0 : ℂ) ^ (3 * k ^ 2 + 5 * k + 2))) = 1 := by
      rw [tsum_eq_single (0 : ℕ) (fun k hk => by
        have h2 : 3 * k ^ 2 + k ≠ 0 := by
          have : 0 < k := Nat.pos_of_ne_zero hk
          positivity
        have h3 : 3 * k ^ 2 + 5 * k + 2 ≠ 0 := by
          have : 0 < k := Nat.pos_of_ne_zero hk
          positivity
        rw [zero_pow h2, zero_pow h3, sub_zero, mul_zero])]
      simp
    rw [hL, hR]
  · rw [jtpTheta]
    have hsumA : Summable (fun n : ℕ => (X ^ 3) ^ ((n : ℤ) ^ 2) * (-X) ^ ((n : ℤ))) :=
      hA.congr (fun n => (jtp_pos_term X n).symm)
    have hsumB : Summable
        (fun n : ℕ => (X ^ 3) ^ ((-((n : ℤ) + 1)) ^ 2) * (-X) ^ (-((n : ℤ) + 1))) :=
      hB.neg.congr (fun n => (jtp_neg_term X hX0 n).symm)
    calc (∑' n : ℤ, (X ^ 3) ^ (n ^ 2) * (-X) ^ n)
        = (∑' n : ℕ, (X ^ 3) ^ ((n : ℤ) ^ 2) * (-X) ^ ((n : ℤ)))
            + (∑' n : ℕ, (X ^ 3) ^ ((-((n : ℤ) + 1)) ^ 2)
                * (-X) ^ (-((n : ℤ) + 1))) :=
          tsum_of_nat_of_neg_add_one (f := fun m : ℤ => (X ^ 3) ^ (m ^ 2) * (-X) ^ m)
            hsumA hsumB
      _ = (∑' n : ℕ, (-1) ^ n * X ^ (3 * n ^ 2 + n))
            + (∑' n : ℕ, -((-1) ^ n * X ^ (3 * n ^ 2 + 5 * n + 2))) := by
          rw [tsum_congr (fun n => jtp_pos_term X n),
            tsum_congr (fun n => jtp_neg_term X hX0 n)]
      _ = (∑' n : ℕ, (-1) ^ n * X ^ (3 * n ^ 2 + n))
            - (∑' n : ℕ, (-1) ^ n * X ^ (3 * n ^ 2 + 5 * n + 2)) := by
          rw [sub_eq_add_neg, tsum_neg]
      _ = ∑' k : ℕ, (-1) ^ k * (X ^ (3 * k ^ 2 + k) - X ^ (3 * k ^ 2 + 5 * k + 2)) := by
          rw [← Summable.tsum_sub
            (f := fun n : ℕ => (-1) ^ n * X ^ (3 * n ^ 2 + n))
            (g := fun n : ℕ => (-1) ^ n * X ^ (3 * n ^ 2 + 5 * n + 2)) hA hB]
          apply tsum_congr
          intro k
          rw [mul_sub]

end Work.Haupt
