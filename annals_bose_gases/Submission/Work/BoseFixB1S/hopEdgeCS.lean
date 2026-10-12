import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- **Edge Cauchy–Schwarz for the hopping layer.**  With `f e = |w e|·√(a e)` and
`g e = √(b e)` the summand is `f e * g e`, so this is the Cauchy–Schwarz inequality
`(∑ f g)² ≤ (∑ f²)(∑ g²)`, followed by `∑ f² = ∑ w²a` (`|w|² = w²`, `(√a)² = a`) and
`∑ g² = ∑ b`, and finally `Real.le_sqrt`. -/
theorem hopEdgeCS {ι : Type*} (s : Finset ι) (a b w : ι → ℝ)
    (ha : ∀ e ∈ s, 0 ≤ a e) (hb : ∀ e ∈ s, 0 ≤ b e) :
    (∑ e ∈ s, |w e| * Real.sqrt (a e * b e))
      ≤ Real.sqrt ((∑ e ∈ s, (w e) ^ 2 * a e) * (∑ e ∈ s, b e)) := by
  set f : ι → ℝ := fun e => |w e| * Real.sqrt (a e)
  set g : ι → ℝ := fun e => Real.sqrt (b e)
  have hLHS : (∑ e ∈ s, |w e| * Real.sqrt (a e * b e)) = ∑ e ∈ s, f e * g e := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [f, g]
    rw [Real.sqrt_mul (ha e he)]
    ring
  have hR1 : (∑ e ∈ s, f e ^ 2) = ∑ e ∈ s, (w e) ^ 2 * a e := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [f]
    rw [mul_pow, sq_abs, Real.sq_sqrt (ha e he)]
  have hR2 : (∑ e ∈ s, g e ^ 2) = ∑ e ∈ s, b e := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [g]
    rw [Real.sq_sqrt (hb e he)]
  rw [hLHS, ← hR1, ← hR2]
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact Finset.sum_mul_sq_le_sq_mul_sq s f g

end Work.BoseFixB1S
