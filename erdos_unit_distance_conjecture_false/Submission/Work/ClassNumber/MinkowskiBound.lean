import Mathlib

namespace Work.ClassNumber

theorem MinkowskiBound (K : Type*) [Field K] [NumberField K] {A : ℝ} (hA : 1 ≤ A)
    (h : NumberField.rootDiscr K ≤ A) :
    (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
          Real.sqrt |((NumberField.discr K : ℤ) : ℝ)|) ≤
      (2 * Real.sqrt A) ^ Module.finrank ℚ K := by
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  -- The number of complex places is at most the degree.
  have hs_le : NumberField.InfinitePlace.nrComplexPlaces K ≤ Module.finrank ℚ K := by
    have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  -- The factor `4 / π` is at most `2`.
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h4pi : (4 : ℝ) / Real.pi ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith
  have h4pi0 : (0 : ℝ) ≤ 4 / Real.pi := by positivity
  -- `(4 / π) ^ s ≤ 2 ^ n`.
  have h1 : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K
      ≤ (2 : ℝ) ^ Module.finrank ℚ K :=
    le_trans (pow_le_pow_left₀ h4pi0 h4pi _)
      (pow_le_pow_right₀ (by norm_num) hs_le)
  -- `n ! / n ^ n ≤ 1`.
  have hnn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K := by positivity
  have h2 : ((Module.finrank ℚ K).factorial : ℝ) /
        ((Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K) ≤ 1 := by
    rw [div_le_one hnn]
    norm_cast
    exact Nat.factorial_le_pow _
  -- From the root discriminant bound, extract `|disc| ≤ A ^ n`.
  rw [NumberField.rootDiscr_def, Int.cast_abs] at h
  have hD0 : (0 : ℝ) ≤ |((NumberField.discr K : ℤ) : ℝ)| := abs_nonneg _
  have hbase : (0 : ℝ) ≤ |((NumberField.discr K : ℤ) : ℝ)| ^ (Module.finrank ℚ K : ℝ)⁻¹ :=
    Real.rpow_nonneg hD0 _
  have hDn : |((NumberField.discr K : ℤ) : ℝ)| ≤ A ^ Module.finrank ℚ K := by
    calc |((NumberField.discr K : ℤ) : ℝ)|
        = (|((NumberField.discr K : ℤ) : ℝ)| ^ (Module.finrank ℚ K : ℝ)⁻¹) ^
            Module.finrank ℚ K :=
          (Real.rpow_inv_natCast_pow hD0 hn.ne').symm
      _ ≤ A ^ Module.finrank ℚ K := by
          rw [← Real.rpow_natCast _ (Module.finrank ℚ K), ← Real.rpow_natCast A _]
          exact Real.rpow_le_rpow hbase h (Nat.cast_nonneg _)
  -- Hence `√|disc| ≤ (√A) ^ n`.
  have h3 : Real.sqrt |((NumberField.discr K : ℤ) : ℝ)| ≤
      (Real.sqrt A) ^ Module.finrank ℚ K := by
    have e1 : (Real.sqrt A) ^ Module.finrank ℚ K
        = A ^ ((Module.finrank ℚ K : ℝ) * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ (Module.finrank ℚ K),
        ← Real.rpow_mul hA0]
      congr 1
      ring
    have e2 : (A ^ Module.finrank ℚ K : ℝ) ^ (1 / 2 : ℝ)
        = A ^ ((Module.finrank ℚ K : ℝ) * (1 / 2)) := by
      rw [← Real.rpow_natCast A (Module.finrank ℚ K), ← Real.rpow_mul hA0]
    rw [Real.sqrt_eq_rpow, e1, ← e2]
    exact Real.rpow_le_rpow hD0 hDn (by norm_num)
  -- Combine the three bounds.
  have hbc : ((Module.finrank ℚ K).factorial : ℝ) /
        ((Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K) *
          Real.sqrt |((NumberField.discr K : ℤ) : ℝ)|
      ≤ 1 * (Real.sqrt A) ^ Module.finrank ℚ K :=
    mul_le_mul h2 h3 (Real.sqrt_nonneg _) zero_le_one
  have hfin := mul_le_mul h1 hbc (by positivity) (by positivity)
  rw [one_mul, ← mul_pow] at hfin
  exact hfin

end Work.ClassNumber
