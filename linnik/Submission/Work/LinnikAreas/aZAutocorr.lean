import Mathlib
import Submission.Work.LinnikAreas.TFDefs
import Submission.Work.LinnikAreas.tsum_int_eq_tsum_nat_add
import Submission.Work.LinnikAreas.summable_aSeq_mul_shift
import Submission.Work.LinnikAreas.aSeq_add_shift_eq

/-!
# Autocorrelation of the Turán–Fejér sequence `aZ`

For `aSeq r 0 = 1`, `aSeq r (n+1) = (1+r) r^n` (extended by `0` to `aZ r` on `ℤ`), we compute
the whole-line autocorrelation

  `∑' p : ℤ, aZ r (p + m) * aZ r p`.

Because `aZ r` vanishes on the negative integers, the summand vanishes for `p < -m` and for
`p < 0`, so the `ℤ`-sum reindexes to an `ℕ`-sum of `n ↦ aSeq r n * aSeq r (n + |m|)`.  Splitting
off the `n = 0` term and summing the residual geometric series of ratio `r^2` gives the closed
form `2/(1-r)` for `m = 0` and `(1+r) r^{|m|-1}/(1-r)` otherwise.
-/

namespace Work.LinnikAreas

open scoped BigOperators

/-- The `ℕ`-indexed shifted autocorrelation of `aSeq`: after peeling off the `n = 0` term the
remaining series is geometric with ratio `r ^ 2`, yielding the closed form. -/
theorem tsum_aSeq_mul_shift (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (c : ℕ) :
    (∑' n : ℕ, aSeq r n * aSeq r (n + c)) = aSeq r c + (1 + r) * r ^ c / (1 - r) := by
  have hs := summable_aSeq_mul_shift r hr0 hr1 c
  rw [hs.tsum_eq_zero_add]
  have htail : (∑' n : ℕ, aSeq r (n + 1) * aSeq r ((n + 1) + c)) = (1 + r) * r ^ c / (1 - r) := by
    have h : (fun n : ℕ => aSeq r (n + 1) * aSeq r ((n + 1) + c))
        = fun n : ℕ => ((1 + r) ^ 2 * r ^ c) * (r ^ 2) ^ n := by
      funext n; exact aSeq_mul_aSeq_succ_succ r c n
    rw [h, tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg r) (by nlinarith)]
    have hr2 : (1 : ℝ) - r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
    have h1r : (1 : ℝ) - r ≠ 0 := by linarith
    rw [div_eq_mul_inv]; field_simp; ring
  rw [htail]
  simp [aSeq_zero]

theorem aZAutocorr (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℤ) :
    (∑' p : ℤ, aZ r (p + m) * aZ r p) =
      (if m = 0 then 2 / (1 - r) else (1 + r) * r ^ (m.natAbs - 1) / (1 - r)) := by
  have key : (∑' p : ℤ, aZ r (p + m) * aZ r p)
      = ∑' n : ℕ, aSeq r n * aSeq r (n + m.natAbs) := by
    by_cases hm : 0 ≤ m
    · -- `m ≥ 0`: the summand vanishes for `p < 0`, reindex by `p = n`.
      have hcast : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg hm
      have h1 : (∑' p : ℤ, aZ r (p + m) * aZ r p)
          = ∑' n : ℕ, aZ r ((n : ℤ) + m) * aZ r (n : ℤ) := by
        rw [tsum_int_eq_tsum_nat_add (fun p => aZ r (p + m) * aZ r p) 0 (fun p hp => by
          rw [aZ_eq_zero_of_neg r hp, mul_zero])]
        simp
      rw [h1]
      refine tsum_congr (fun n => ?_)
      have hc2 : ((n : ℤ) + m) = ((n + m.natAbs : ℕ) : ℤ) := by rw [Nat.cast_add, hcast]
      rw [hc2]
      simp only [aZ_ofNat]
      ring
    · -- `m < 0`: the summand vanishes for `p < -m`, reindex by `p = -m + n`.
      have hm' : m < 0 := not_le.mp hm
      have hcast : ((m.natAbs : ℕ) : ℤ) = -m := by
        rw [← Int.natAbs_neg m]; exact Int.natAbs_of_nonneg (by linarith)
      have h1 : (∑' p : ℤ, aZ r (p + m) * aZ r p)
          = ∑' n : ℕ,
              aZ r (((m.natAbs : ℤ)) + (n : ℤ) + m) * aZ r ((m.natAbs : ℤ) + (n : ℤ)) := by
        rw [tsum_int_eq_tsum_nat_add (fun p => aZ r (p + m) * aZ r p) ((m.natAbs : ℕ) : ℤ)]
        · intro p hp
          have hp2 : p < -m := by rw [← hcast]; exact hp
          rw [aZ_eq_zero_of_neg r (by linarith : p + m < 0), zero_mul]
      rw [h1]
      refine tsum_congr (fun n => ?_)
      have hNm : ((m.natAbs : ℕ) : ℤ) + (n : ℤ) + m = (n : ℤ) := by rw [hcast]; ring
      have hc2 : ((m.natAbs : ℕ) : ℤ) + (n : ℤ) = ((m.natAbs + n : ℕ) : ℤ) := by
        rw [Nat.cast_add]
      rw [hNm, hc2]
      simp only [aZ_ofNat]
      rw [show m.natAbs + n = n + m.natAbs by omega]
  rw [key, tsum_aSeq_mul_shift r hr0 hr1 m.natAbs]
  rw [aSeq_add_shift_eq r hr1 m.natAbs]
  simp only [Int.natAbs_eq_zero]

end Work.LinnikAreas
