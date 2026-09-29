import Mathlib

/-! # Tail bound for the logarithmic geometric series

For `‖q‖ ≤ R < 1` the series `∑ⱼ log ‖1 + q^{j+k+1}‖` is dominated by the geometric tail
`∑ⱼ R^{j+k+1} = R^{k+1}/(1-R)`.

The pointwise input is `log ‖1 + z‖ ≤ ‖z‖` (`log_norm_one_add_le`), and both series are
summable: the geometric one because `R < 1`, the logarithmic one by
`Summable.summable_log_norm_one_add` applied to `∑ⱼ ‖q^{j+k+1}‖` (shift of `∑ⱼ ‖q‖^j`).
-/

open scoped BigOperators

namespace Work.ANum

/-- `log ‖1 + z‖ ≤ ‖z‖` for every complex `z`. -/
lemma log_norm_one_add_le (z : ℂ) : Real.log ‖(1 : ℂ) + z‖ ≤ ‖z‖ := by
  rcases eq_or_lt_of_le (norm_nonneg ((1 : ℂ) + z)) with h | h
  · rw [← h, Real.log_zero]
    positivity
  · rw [Real.log_le_iff_le_exp h]
    calc ‖(1 : ℂ) + z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
      _ = 1 + ‖z‖ := by simp
      _ = ‖z‖ + 1 := by ring
      _ ≤ Real.exp ‖z‖ := Real.add_one_le_exp ‖z‖

theorem tsum_log_geom_tail {q : ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) (hq : ‖q‖ ≤ R) (k : ℕ) :
    ∑' j : ℕ, Real.log ‖(1 : ℂ) + q ^ (j + k + 1)‖ ≤ R ^ (k + 1) / (1 - R) := by
  have hRlt1 : ‖q‖ < 1 := lt_of_le_of_lt hq hR1
  -- split off the leading factor `R^(k+1)` from the geometric tail
  have hpowR : ∀ j : ℕ, R ^ (j + k + 1) = R ^ (k + 1) * R ^ j := by
    intro j
    rw [← pow_add]
    congr 1
    omega
  -- pointwise domination
  have hle : ∀ j : ℕ, Real.log ‖(1 : ℂ) + q ^ (j + k + 1)‖ ≤ R ^ (j + k + 1) := by
    intro j
    refine (log_norm_one_add_le (q ^ (j + k + 1))).trans ?_
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg q) hq (j + k + 1)
  -- summability of the geometric tail
  have hsumm_g : Summable (fun j : ℕ => R ^ (j + k + 1)) := by
    have h1 : Summable (fun j : ℕ => R ^ (k + 1) * R ^ j) :=
      (summable_geometric_of_lt_one hR0 hR1).mul_left (R ^ (k + 1))
    exact h1.congr (fun j => (hpowR j).symm)
  -- summability of the logarithmic series
  have hsumm_f : Summable (fun j : ℕ => Real.log ‖(1 : ℂ) + q ^ (j + k + 1)‖) := by
    have hqf : Summable (fun j : ℕ => q ^ (j + k + 1)) := by
      have h2 : Summable (fun j : ℕ => q ^ (j + (k + 1))) :=
        (summable_nat_add_iff (k + 1)).2 (summable_geometric_iff_norm_lt_one.mpr hRlt1)
      exact h2.congr (fun j => by rw [Nat.add_assoc])
    exact hqf.norm.summable_log_norm_one_add
  -- value of the geometric tail
  have hval : ∑' j : ℕ, R ^ (j + k + 1) = R ^ (k + 1) / (1 - R) := by
    have h1 : (∑' j : ℕ, R ^ (j + k + 1)) = ∑' j : ℕ, R ^ (k + 1) * R ^ j :=
      tsum_congr hpowR
    rw [h1, tsum_mul_left, tsum_geometric_of_lt_one hR0 hR1, div_eq_mul_inv]
  calc ∑' j : ℕ, Real.log ‖(1 : ℂ) + q ^ (j + k + 1)‖
      ≤ ∑' j : ℕ, R ^ (j + k + 1) := hsumm_f.tsum_le_tsum hle hsumm_g
    _ = R ^ (k + 1) / (1 - R) := hval

end Work.ANum
