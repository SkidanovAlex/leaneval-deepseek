import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_natpairs
import Submission.Commons.Analysis.FriedlanderIwaniec.sum_natSqrt_sub_pow_four_sub_kappa_bound

open scoped BigOperators

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The number of natural pairs `(a, b)` with `a ^ 2 + b ^ 4 ≤ x` is asymptotic to
`C * x ^ (3/4)`, where `C = ∫ u in (0)..1, Real.sqrt (1 - u ^ 4)`, with an error
`O(Real.sqrt x)`.

This combines the exact count
`card_sq_add_pow_four_natpairs` (the count equals the sum over `c ≤ x ^ (1/4)` of
`Nat.sqrt (x - c ^ 4) + 1`) with the analytic estimate
`sum_natSqrt_sub_pow_four_sub_kappa_bound` for the bare sum `∑ Nat.sqrt (x - c ^ 4)`.
The extra `+ 1` in each summand contributes `M + 1 ≤ 2 * Real.sqrt x`. -/
lemma card_sq_add_pow_four_natpairs_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      |(({p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x}.ncard : ℕ) : ℝ) -
        (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)| ≤ C * Real.sqrt x := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.Analysis.FriedlanderIwaniec.sum_natSqrt_sub_pow_four_sub_kappa_bound
  refine ⟨C0 + 2, by linarith, ?_⟩
  intro x hx
  set X : ℝ := (x : ℝ) with hXdef
  have hX1 : (1 : ℝ) ≤ X := by rw [hXdef]; exact_mod_cast hx
  have hX0 : (0 : ℝ) ≤ X := le_trans zero_le_one hX1
  set I : ℝ := ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) with hIdef
  set M : ℕ := Nat.sqrt (Nat.sqrt x) + 1 with hMdef
  -- exact count as `(∑ c < M, Nat.sqrt (x - c ^ 4)) + M`
  have hcountnat : ({p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x}.ncard)
      = (∑ c ∈ Finset.range M, Nat.sqrt (x - c ^ 4)) + M := by
    rw [card_sq_add_pow_four_natpairs]
    rw [← hMdef]
    rw [Finset.sum_add_distrib]
    simp
  have hcount : (({p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x}.ncard : ℕ) : ℝ)
      = (((∑ c ∈ Finset.range M, Nat.sqrt (x - c ^ 4)) : ℕ) : ℝ) + (M : ℝ) := by
    rw [hcountnat]; push_cast; ring
  -- the analytic estimate for the bare sum
  have hTbnd : |(((∑ c ∈ Finset.range M, Nat.sqrt (x - c ^ 4)) : ℕ) : ℝ) -
      I * X ^ (3 / 4 : ℝ)| ≤ C0 * Real.sqrt X := by
    simpa only [hMdef, hIdef, hXdef] using hC0 x hx
  -- the number of terms is at most `2 * Real.sqrt X`
  have hM_le : (M : ℝ) ≤ 2 * Real.sqrt X := by
    have h1 : (Nat.sqrt (Nat.sqrt x) : ℝ) ≤ (Nat.sqrt x : ℝ) := by
      exact_mod_cast Nat.sqrt_le_self (Nat.sqrt x)
    have h2 : (Nat.sqrt x : ℝ) ≤ Real.sqrt X := by
      rw [Real.le_sqrt (by positivity) hX0]
      rw [hXdef]
      exact_mod_cast Nat.sqrt_le' x
    have h3 : (1 : ℝ) ≤ Real.sqrt X := Real.one_le_sqrt.mpr hX1
    have hMeq : (M : ℝ) = (Nat.sqrt (Nat.sqrt x) : ℝ) + 1 := by
      rw [hMdef]; push_cast; ring
    rw [hMeq]; linarith
  -- triangle inequality, splitting off the `M` copies of `1`
  have htri : |(({p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x}.ncard : ℕ) : ℝ) - I * X ^ (3 / 4 : ℝ)|
      ≤ |(((∑ c ∈ Finset.range M, Nat.sqrt (x - c ^ 4)) : ℕ) : ℝ) - I * X ^ (3 / 4 : ℝ)|
        + (M : ℝ) := by
    rw [hcount]
    rw [show ((((∑ c ∈ Finset.range M, Nat.sqrt (x - c ^ 4)) : ℕ) : ℝ) + (M : ℝ))
        - I * X ^ (3 / 4 : ℝ)
        = ((((∑ c ∈ Finset.range M, Nat.sqrt (x - c ^ 4)) : ℕ) : ℝ) - I * X ^ (3 / 4 : ℝ))
          + (M : ℝ) by ring]
    have h2 := abs_add_le
      ((((∑ c ∈ Finset.range M, Nat.sqrt (x - c ^ 4)) : ℕ) : ℝ) - I * X ^ (3 / 4 : ℝ)) (M : ℝ)
    rwa [abs_of_nonneg (show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M)] at h2
  calc |(({p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x}.ncard : ℕ) : ℝ) - I * X ^ (3 / 4 : ℝ)|
      ≤ |(((∑ c ∈ Finset.range M, Nat.sqrt (x - c ^ 4)) : ℕ) : ℝ) - I * X ^ (3 / 4 : ℝ)|
        + (M : ℝ) := htri
    _ ≤ C0 * Real.sqrt X + 2 * Real.sqrt X := by linarith [hTbnd, hM_le]
    _ = (C0 + 2) * Real.sqrt X := by ring

end Commons.NumberTheory.FriedlanderIwaniec
