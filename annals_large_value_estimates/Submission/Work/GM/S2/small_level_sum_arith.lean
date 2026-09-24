import Mathlib
import Submission.Work.GM.S2.pair_sum_defs

namespace Work.GM.S2

/-- Arithmetic estimate underlying the "small level" contribution to the `S₂` pair sum.

Each summand is a constant, so the left-hand side is `K` times a single term.  Since
`M N = N^{6/5}` and `η j ≥ 25`, the factor `(M N)^{-η j}` is at most `N^{-1}`, and the
number of summands `K` is at most `N^{δ/4}`; the first term of the bracket absorbs the
whole sum. -/
theorem small_level_sum_arith
    (N K : ℕ) (R Cs : ℝ) (j : ℕ) (δ η : ℝ)
    (hR : 0 ≤ R) (hN : 1 ≤ N) (hδ : 0 < δ) (hη : 0 < η) (hCs : 0 < Cs)
    (hKle : (K : ℝ) ≤ (N : ℝ) ^ (δ / 4)) (hηj : 25 ≤ η * (j : ℝ)) :
    (∑ _kk ∈ Finset.range K, (Cs * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ)))) ^ 2 * R ^ 2)
      ≤ Cs ^ 2 * (N : ℝ) ^ (δ / 4) * (R ^ 2 / (N : ℝ)
          + Submission.LargeValues.M N * R ^ ((7 : ℝ) / 4) / (N : ℝ) ^ 2
          + (Submission.LargeValues.M N) ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / (N : ℝ)) := by
  set A : ℝ := (N : ℝ) with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef]; exact_mod_cast hN
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hAnonneg : (0 : ℝ) ≤ A := le_of_lt hApos
  have hMpos : 0 < Submission.LargeValues.M N := Submission.LargeValues.M_pos hN
  have hMnonneg : 0 ≤ Submission.LargeValues.M N := le_of_lt hMpos
  have hMN : Submission.LargeValues.M N = A ^ (6 / 5 : ℝ) := by
    simp [Submission.LargeValues.M, hAdef]
  -- The key point: `(M N)^{-η j}` squared is at most `N⁻¹`.
  have hkey : ((Submission.LargeValues.M N) ^ (-(η * (j : ℝ)))) ^ 2 ≤ A⁻¹ := by
    have hbase : ((Submission.LargeValues.M N) ^ (-(η * (j : ℝ)))) ^ 2
        = A ^ (-((12 / 5 : ℝ) * (η * (j : ℝ)))) := by
      rw [hMN]
      rw [← Real.rpow_mul hAnonneg (6 / 5 : ℝ) (-(η * (j : ℝ)))]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hAnonneg ((6 / 5 : ℝ) * (-(η * (j : ℝ)))) ((2 : ℕ) : ℝ)]
      congr 1
      push_cast
      ring
    rw [hbase, ← Real.rpow_neg_one A]
    apply Real.rpow_le_rpow_of_exponent_le hA1
    nlinarith [hηj]
  -- Hence a single summand is at most `Cs² R² / N`.
  have hterm : (Cs * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ)))) ^ 2 * R ^ 2
      ≤ Cs ^ 2 * R ^ 2 / A := by
    have hx : 0 ≤ Cs ^ 2 * R ^ 2 := by positivity
    calc (Cs * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ)))) ^ 2 * R ^ 2
        = Cs ^ 2 * R ^ 2 * (((Submission.LargeValues.M N) ^ (-(η * (j : ℝ)))) ^ 2) := by ring
      _ ≤ Cs ^ 2 * R ^ 2 * A⁻¹ := mul_le_mul_of_nonneg_left hkey hx
      _ = Cs ^ 2 * R ^ 2 / A := by rw [div_eq_mul_inv]
  have hD0 : (0 : ℝ) ≤ Cs ^ 2 * R ^ 2 / A := by positivity
  have ht1 : 0 ≤ Submission.LargeValues.M N * R ^ ((7 : ℝ) / 4) / A ^ 2 := by
    apply div_nonneg
    · exact mul_nonneg hMnonneg (Real.rpow_nonneg hR _)
    · positivity
  have ht2 : 0 ≤ (Submission.LargeValues.M N) ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A := by
    apply div_nonneg
    · exact mul_nonneg (Real.rpow_nonneg hMnonneg _) (Real.rpow_nonneg hR _)
    · exact hAnonneg
  have hbracket : R ^ 2 / A ≤ R ^ 2 / A
      + Submission.LargeValues.M N * R ^ ((7 : ℝ) / 4) / A ^ 2
      + (Submission.LargeValues.M N) ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A := by
    linarith
  have hCA : 0 ≤ Cs ^ 2 * A ^ (δ / 4) :=
    mul_nonneg (sq_nonneg Cs) (Real.rpow_nonneg hAnonneg _)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (K : ℝ) * ((Cs * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ)))) ^ 2 * R ^ 2)
      ≤ (K : ℝ) * (Cs ^ 2 * R ^ 2 / A) := mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg K)
    _ ≤ A ^ (δ / 4) * (Cs ^ 2 * R ^ 2 / A) := mul_le_mul_of_nonneg_right hKle hD0
    _ ≤ Cs ^ 2 * A ^ (δ / 4) * (R ^ 2 / A + Submission.LargeValues.M N * R ^ ((7 : ℝ) / 4) / A ^ 2
          + (Submission.LargeValues.M N) ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / A) := by
        rw [show A ^ (δ / 4) * (Cs ^ 2 * R ^ 2 / A) = (Cs ^ 2 * A ^ (δ / 4)) * (R ^ 2 / A) by ring]
        exact mul_le_mul_of_nonneg_left hbracket hCA

end Work.GM.S2
