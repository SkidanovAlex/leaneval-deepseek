import Mathlib

/-!
# Powers of `log` are dominated by every positive power

For fixed `m : ℕ` and `ε > 0`, `(log A + 1)^m ≤ A^ε` for all large `A ≥ 1`.
-/

set_option autoImplicit false

namespace Work.HP.Sig2

theorem log_pow_le_rpow (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → (Real.log A + 1) ^ m ≤ A ^ ε := by
  set δ : ℝ := ε / (2 * ((m : ℝ) + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδhalf : δ * (m : ℝ) ≤ ε / 2 := by
    have hden : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
    rw [hδdef, div_mul_eq_mul_div]
    rw [div_le_iff₀ hden]
    nlinarith [hε, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
  refine ⟨max 4 (max 1 (((1 / δ) + 1) ^ ((2 * (m : ℝ)) / ε))),
    le_trans (by norm_num) (le_max_left 4 _), ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := le_trans (le_trans (by norm_num) (le_max_left 4 _)) hA
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hAnonneg : 0 ≤ A := le_of_lt hApos
  have hlog : Real.log A ≤ (1 / δ) * A ^ δ := by
    have h := Real.log_le_rpow_div hAnonneg hδpos
    rw [div_eq_inv_mul] at h
    simpa using h
  have hpowδ1 : 1 ≤ A ^ δ := Real.one_le_rpow hA1 (le_of_lt hδpos)
  have h2 : Real.log A + 1 ≤ ((1 / δ) + 1) * A ^ δ := by nlinarith [hlog, hpowδ1]
  have h3 : (Real.log A + 1) ^ m ≤ (((1 / δ) + 1) * A ^ δ) ^ m :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg hA1]) h2 m
  have h4 : (((1 / δ) + 1) * A ^ δ) ^ m = ((1 / δ) + 1) ^ m * A ^ (δ * (m : ℝ)) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hAnonneg]
  have h5 : A ^ (δ * (m : ℝ)) ≤ A ^ (ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hA1 hδhalf
  have h6 : ((1 / δ) + 1) ^ m ≤ A ^ (ε / 2) := by
    have hA0 : ((1 / δ) + 1) ^ ((2 * (m : ℝ)) / ε) ≤ A :=
      le_trans (le_trans (le_max_right 1 _) (le_max_right 4 _)) hA
    have hmul : (2 * (m : ℝ)) / ε * (ε / 2) = (m : ℝ) := by
      field_simp
    have : (((1 / δ) + 1) ^ ((2 * (m : ℝ)) / ε)) ^ (ε / 2) ≤ A ^ (ε / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hA0 (by positivity)
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (1 / δ) + 1), hmul,
      Real.rpow_natCast] at this
    exact this
  have h7 : ((1 / δ) + 1) ^ m * A ^ (ε / 2) ≤ A ^ (ε / 2) * A ^ (ε / 2) :=
    mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hAnonneg _)
  have h8 : A ^ (ε / 2) * A ^ (ε / 2) = A ^ ε := by
    rw [← Real.rpow_add hApos]
    congr 1
    ring
  calc (Real.log A + 1) ^ m ≤ (((1 / δ) + 1) * A ^ δ) ^ m := h3
    _ = ((1 / δ) + 1) ^ m * A ^ (δ * (m : ℝ)) := h4
    _ ≤ ((1 / δ) + 1) ^ m * A ^ (ε / 2) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ ≤ A ^ (ε / 2) * A ^ (ε / 2) := h7
    _ = A ^ ε := h8

end Work.HP.Sig2
