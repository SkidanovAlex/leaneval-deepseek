import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Commons.Analysis.SpecialFunctions.Harmonic

/-- The `n`-th harmonic number, viewed in `ℝ`, is the sum of the reciprocals
`1/j` for `j = 1, …, n`. -/
lemma harmonic_cast_eq_sum (m : ℕ) :
    (harmonic m : ℝ) = ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (j : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp [one_div]

theorem harmonic_log_bounds :
    (∀ m : ℕ, 1 ≤ m → Real.log (m : ℝ) ≤ ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (j : ℝ))
    ∧ (∀ m : ℕ, 1 ≤ m → (∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (j : ℝ)) ≤ 1 + Real.log (m : ℝ))
    ∧ (∀ m : ℕ, 1 ≤ m →
        (∑ j ∈ Finset.Icc 1 (m + 1), (1 : ℝ) / (j : ℝ)) - Real.log ((m + 1 : ℕ) : ℝ)
          ≤ (∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (j : ℝ)) - Real.log (m : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `log m ≤ log (m+1) ≤ H_m`
    intro m hm
    have h := log_add_one_le_harmonic m
    rw [harmonic_cast_eq_sum] at h
    refine (Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) ?_).trans h
    push_cast
    linarith
  · -- `H_m ≤ 1 + log m`
    intro m hm
    rw [← harmonic_cast_eq_sum]
    exact harmonic_le_one_add_log m
  · -- `H_{m+1} - log (m+1) ≤ H_m - log m`, since `1/(m+1) ≤ log (m+1) - log m`
    intro m hm
    have hS : (∑ j ∈ Finset.Icc 1 (m + 1), (1 : ℝ) / (j : ℝ))
        = (∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (j : ℝ)) + (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    rw [hS]
    have hkey : (1 : ℝ) / ((m + 1 : ℕ) : ℝ)
        ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hmp1pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hdiv : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / (m : ℝ) := div_pos hmp1pos hmpos
      have h := Real.one_sub_inv_le_log_of_pos hdiv
      rw [Real.log_div (ne_of_gt hmp1pos) (ne_of_gt hmpos), inv_div] at h
      have heq : 1 - (m : ℝ) / ((m + 1 : ℕ) : ℝ)
          = (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        rw [eq_div_iff (by positivity : (((m + 1 : ℕ) : ℝ)) ≠ 0)]
        rw [sub_mul, div_mul_cancel₀ _ (by positivity : (((m + 1 : ℕ) : ℝ)) ≠ 0)]
        push_cast
        ring
      linarith [h, heq]
    linarith

end Commons.Analysis.SpecialFunctions.Harmonic