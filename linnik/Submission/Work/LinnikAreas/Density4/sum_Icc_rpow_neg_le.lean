import Mathlib

namespace Work.LinnikAreas.Density4

/-- Sum bound for `m^{-σ}` over `1 ≤ m ≤ Y`, for `σ ≤ 1`:
`Σ_{m=1}^{Y} m^{-σ} ≤ Y^{1-σ} (1 + log Y)`.

Each term is bounded by `Y^{1-σ}/m` (since `m^{1-σ} ≤ Y^{1-σ}` for `m ≤ Y` and `1 - σ ≥ 0`),
and the harmonic sum `Σ_{m=1}^{Y} 1/m` is at most `1 + log Y`. -/
lemma sum_Icc_rpow_neg_le {Y : ℕ} (hY : 1 ≤ Y) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∑ m ∈ Finset.Icc 1 Y, (m : ℝ) ^ (-σ) ≤ (Y : ℝ) ^ (1 - σ) * (1 + Real.log (Y : ℝ)) := by
  have hY0 : (0:ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hexp : 0 ≤ 1 - σ := by linarith
  -- Per-term bound: `m^{-σ} ≤ Y^{1-σ} · m^{-1}`.
  have hterm : ∀ m ∈ Finset.Icc 1 Y, (m:ℝ)^(-σ) ≤ (Y:ℝ)^(1-σ) * (m:ℝ)^(-1:ℝ) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmY : m ≤ Y := (Finset.mem_Icc.mp hm).2
    have hm0 : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
    have hmle : (m:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hmY
    have hpow : (m:ℝ)^(1-σ) ≤ (Y:ℝ)^(1-σ) := Real.rpow_le_rpow hm0.le hmle hexp
    have hstep := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hm0.le (-1:ℝ))
    have heq : (m:ℝ)^(-σ) = (m:ℝ)^(1-σ) * (m:ℝ)^(-1:ℝ) := by
      rw [← Real.rpow_add hm0]
      congr 1
      ring
    rw [heq]
    exact hstep
  -- Harmonic bound `Σ_{m=1}^{Y} 1/m ≤ 1 + log Y`.
  have hH : ∑ m ∈ Finset.Icc 1 Y, (m:ℝ)^(-1:ℝ) ≤ 1 + Real.log (Y:ℝ) := by
    have hcast : (harmonic Y : ℝ) = ∑ m ∈ Finset.Icc 1 Y, (m:ℝ)⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    simp_rw [Real.rpow_neg_one]
    rw [← hcast]
    exact harmonic_le_one_add_log Y
  calc ∑ m ∈ Finset.Icc 1 Y, (m:ℝ)^(-σ)
      ≤ ∑ m ∈ Finset.Icc 1 Y, (Y:ℝ)^(1-σ) * (m:ℝ)^(-1:ℝ) := Finset.sum_le_sum hterm
    _ = (Y:ℝ)^(1-σ) * ∑ m ∈ Finset.Icc 1 Y, (m:ℝ)^(-1:ℝ) := by rw [Finset.mul_sum]
    _ ≤ (Y:ℝ)^(1-σ) * (1 + Real.log (Y:ℝ)) :=
        mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hY0.le _)

end Work.LinnikAreas.Density4
