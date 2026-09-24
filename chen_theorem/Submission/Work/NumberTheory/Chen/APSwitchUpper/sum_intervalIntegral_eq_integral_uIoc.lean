import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Work.NumberTheory.Chen.APSwitchUpper

/-- **Truncated interval integrals add up to the integral of the sum.**
Each `g j` vanishes on `[u j, ∞)` and `u j ≤ M`, so on `uIoc a M` the `j`-th
summand is supported in `uIoc a (u j)`, where the set integral agrees with the
interval integral `∫ x in a..u j, g j x` (for `u j < a` both sides vanish). -/
theorem sum_intervalIntegral_eq_integral_uIoc
    (S : Finset ℕ) (g : ℕ → ℝ → ℝ) (u : ℕ → ℝ) (a M : ℝ)
    (hu : ∀ j ∈ S, u j ≤ M)
    (hint : ∀ j ∈ S, ∀ p q : ℝ, IntervalIntegrable (g j) MeasureTheory.volume p q)
    (hsupp : ∀ j ∈ S, ∀ x : ℝ, u j ≤ x → g j x = 0) :
    (∑ j ∈ S, ∫ x in a..u j, g j x) = ∫ x in Set.uIoc a M, ∑ j ∈ S, g j x := by
  have hterm : ∀ j ∈ S, (∫ x in a..u j, g j x) = ∫ x in Set.uIoc a M, g j x := by
    intro j hj
    have hujM : u j ≤ M := hu j hj
    by_cases haj : a ≤ u j
    · -- the truncation point is above `a`: split `(a, M] = (a, u j] ∪ (u j, M]`
      have haM : a ≤ M := le_trans haj hujM
      have hzero : ∫ x in u j..M, g j x = 0 := by
        have h : ∫ x in u j..M, g j x = ∫ x in u j..M, (0:ℝ) :=
          intervalIntegral.integral_congr (fun x hx => by
            have hx' : u j ≤ x := by
              have hmem := hx
              rw [Set.uIcc_of_le hujM, Set.mem_Icc] at hmem
              exact hmem.1
            exact hsupp j hj x hx')
        rw [h, intervalIntegral.integral_zero]
      have hM : ∫ x in a..M, g j x = ∫ x in Set.uIoc a M, g j x := by
        rw [Set.uIoc_of_le haM, intervalIntegral.integral_of_le haM]
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (hint j hj a (u j)) (hint j hj (u j) M)
      rw [← hM, ← hadj, hzero, add_zero]
    · -- the truncation point is below `a`: both integrals vanish
      have hlt : u j < a := not_le.mp haj
      have hzero2 : ∫ x in u j..a, g j x = 0 := by
        have h : ∫ x in u j..a, g j x = ∫ x in u j..a, (0:ℝ) :=
          intervalIntegral.integral_congr (fun x hx => by
            have hx' : u j ≤ x := by
              have hmem := hx
              rw [Set.uIcc_of_le (le_of_lt hlt), Set.mem_Icc] at hmem
              exact hmem.1
            exact hsupp j hj x hx')
        rw [h, intervalIntegral.integral_zero]
      have hL : ∫ x in a..u j, g j x = 0 := by
        rw [intervalIntegral.integral_symm (u j) a, hzero2, neg_zero]
      have hR : ∫ x in Set.uIoc a M, g j x = 0 := by
        have h : ∫ x in Set.uIoc a M, g j x = ∫ x in Set.uIoc a M, (0:ℝ) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_uIoc (fun x hx => by
            have hx' := hx
            rw [Set.uIoc, Set.mem_Ioc] at hx'
            exact hsupp j hj x
              (le_of_lt (lt_of_le_of_lt (le_min (le_of_lt hlt) (hu j hj)) hx'.1)))
        rw [h]; simp
      rw [hL, hR]
  -- each summand is integrable on `uIoc a M`
  have hInt : ∀ j ∈ S, MeasureTheory.IntegrableOn (g j) (Set.uIoc a M) MeasureTheory.volume := by
    intro j hj
    rcases hint j hj a M with ⟨h1, h2⟩
    by_cases haM : a ≤ M
    · rwa [Set.uIoc_of_le haM]
    · have hMa : M ≤ a := le_of_lt (not_le.mp haM)
      have he : Set.uIoc a M = Set.Ioc M a := by
        simp only [Set.uIoc, min_eq_right hMa, max_eq_left hMa]
      rw [he]; exact h2
  calc (∑ j ∈ S, ∫ x in a..u j, g j x)
      = ∑ j ∈ S, ∫ x in Set.uIoc a M, g j x := Finset.sum_congr rfl (fun j hj => hterm j hj)
    _ = ∫ x in Set.uIoc a M, ∑ j ∈ S, g j x :=
        (MeasureTheory.integral_finsetSum S hInt).symm

end Work.NumberTheory.Chen.APSwitchUpper
