import Mathlib

namespace Work.A7

/--
Tiling identity for interval integrals over real intervals with integer endpoints:
for a continuous integrand `g : ℝ → ℂ` and integers `a ≤ b`, the integral over
`[(a : ℝ), (b : ℝ)]` is the sum of the integrals over the unit intervals
`[(n : ℝ), (n : ℝ) + 1]` for `n ∈ Finset.Ico a b`.

This is the `ℤ`-indexed refinement of `intervalIntegral.sum_integral_adjacent_intervals_Ico`
(Mathlib, `ℕ`-indexed), proved by induction on `b ≥ a` using additivity of the
interval integral over adjacent intervals.
-/
theorem integral_Icc_eq_sum_Ico_unit (g : ℝ → ℂ) (hg : Continuous g) {a b : ℤ} (hab : a ≤ b) :
    ∫ t in (a : ℝ)..(b : ℝ), g t
      = ∑ n ∈ Finset.Ico a b, ∫ t in (n : ℝ)..((n : ℝ) + 1), g t := by
  refine Int.leInduction (m := a)
    (motive := fun n _ => ∫ t in (a : ℝ)..(n : ℝ), g t
      = ∑ j ∈ Finset.Ico a n, ∫ t in (j : ℝ)..((j : ℝ) + 1), g t) ?_ ?_ b hab
  · simp
  · intro k hak ih
    have hcast : (((k + 1 : ℤ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast, ← intervalIntegral.integral_add_adjacent_intervals
      (a := (a : ℝ)) (b := (k : ℝ)) (c := (k : ℝ) + 1)
      (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _), ih]
    have hins : Finset.Ico a (k + 1) = insert k (Finset.Ico a k) := by
      rw [show (k + 1 : ℤ) = Order.succ k by simp, Finset.Ico_succ_right_eq_Icc]
      exact (Finset.Ico_insert_right hak).symm
    have hnotmem : k ∉ Finset.Ico a k := by simp [Finset.mem_Ico]
    rw [hins, Finset.sum_insert hnotmem]
    ring

end Work.A7
