import Mathlib

namespace Work.CPull

/-- If `‖a n‖ ≤ K (n+1) qⁿ` with `0 ≤ q < 1`, then `a` is summable. -/
theorem summable_geom_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {a : ℕ → E} {K q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1)
    (h : ∀ n : ℕ, ‖a n‖ ≤ K * ((n : ℝ) + 1) * q ^ n) : Summable a := by
  have hqnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq]
  have h1 : Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm
  have h2 : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_norm_lt_one hqnorm
  have hg : Summable (fun n : ℕ => K * ((n : ℝ) + 1) * q ^ n) :=
    ((h1.add h2).mul_left K).congr (fun n => by ring)
  exact hg.of_norm_bounded h

end Work.CPull
