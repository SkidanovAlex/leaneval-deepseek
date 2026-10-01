import Mathlib
import Submission.Work.LinnikAreas.Density4.MuSqTotientDefs

/-!
# The partial sums `Σ_{j ≤ i} p^j · h(p^j)` for a prime `p`

For a prime `p` the weight `hh` satisfies `hh(p⁰) = 1`, `hh(p¹) = 1/(p(p-1))`,
`hh(p²) = -1/(p(p-1))` and `hh(p^j) = 0` for `j ≥ 3`.  Hence

`Σ_{j=0}^{i} p^j · hh(p^j) = 1 + 1/(p-1) - p/(p-1) = 0` for `i ≥ 2`,

while the partial sums for `i = 0, 1` are `1` and `1 + 1/(p-1) = p/(p-1)`.
-/

open Finset BigOperators

namespace Work.LinnikAreas.Density4

noncomputable section

/-- `Σ_{j ≤ i} p^j · hh(p^j)` equals `1`, `p/(p-1)`, `0` according as
`i = 0`, `i = 1`, `i ≥ 2`. -/
theorem hh_prime_pow_sum (p i : ℕ) (hp : Nat.Prime p) :
    (∑ j ∈ Finset.range (i + 1), ((p : ℝ) ^ j) * hh (p ^ j))
      = if i = 0 then 1 else if i = 1 then (p : ℝ) / ((p : ℝ) - 1) else 0 := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  have h0 : ((p : ℝ) ^ (0 : ℕ)) * hh (p ^ (0 : ℕ)) = 1 := by
    simp [hh_one]
  have h1 : ((p : ℝ) ^ (1 : ℕ)) * hh (p ^ (1 : ℕ)) = 1 / ((p : ℝ) - 1) := by
    simp only [pow_one]
    rw [hh_prime p hp, cc]
    field_simp
  have h2 : ((p : ℝ) ^ (2 : ℕ)) * hh (p ^ (2 : ℕ)) = -(p : ℝ) / ((p : ℝ) - 1) := by
    rw [hh_prime_sq p hp, cc]
    field_simp
  have h3 : ∀ j, 3 ≤ j → ((p : ℝ) ^ j) * hh (p ^ j) = 0 := by
    intro j hj
    rw [hh_prime_pow p j hp hj, mul_zero]
  by_cases hi0 : i = 0
  · subst hi0
    rw [Finset.sum_range_one, h0, if_pos rfl]
  · by_cases hi1 : i = 1
    · subst hi1
      rw [show (1 : ℕ) + 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
      rw [if_neg (by norm_num : ¬ ((1 : ℕ) = 0)), if_pos rfl]
      field_simp
      ring
    · have hi2 : 2 ≤ i := by omega
      have hsplit : ∑ j ∈ Finset.range (i + 1), ((p : ℝ) ^ j) * hh (p ^ j)
          = ∑ j ∈ Finset.range 3, ((p : ℝ) ^ j) * hh (p ^ j)
            + ∑ j ∈ Finset.range (i - 2), ((p : ℝ) ^ (3 + j)) * hh (p ^ (3 + j)) := by
        rw [show i + 1 = 3 + (i - 2) from by omega, Finset.sum_range_add]
      rw [hsplit]
      have hz : ∑ j ∈ Finset.range (i - 2), ((p : ℝ) ^ (3 + j)) * hh (p ^ (3 + j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact h3 (3 + j) (by omega)
      rw [hz, add_zero]
      have hsum3 : ∑ j ∈ Finset.range 3, ((p : ℝ) ^ j) * hh (p ^ j)
          = 1 + 1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) - 1) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2]
        ring
      rw [hsum3, if_neg hi0, if_neg hi1]
      field_simp
      ring

end

end Work.LinnikAreas.Density4
