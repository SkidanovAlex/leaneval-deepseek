import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

/-- **The mean-value drop bound.**  If `f` has derivative `f'` on the interval `[a,b]` and
`f' ≥ -C` there, then `f` decreases by at most `C` per unit length: `f a - C (b - a) ≤ f b`.
(Multiply by nothing: `f b - f a ≥ -C (b - a)` by the mean value theorem.) -/
theorem spread_drop_bound {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hC : ∀ t ∈ Set.Icc a b, -C ≤ f' t) : f a - C * (b - a) ≤ f b := by
  -- Fencing: `-f` is bounded above by the affine function of slope `C` through `(a, -f a)`.
  have key : ∀ x ∈ Set.Icc a b, -f x ≤ -f a + C * (x - a) := by
    refine image_le_of_deriv_right_le_deriv_boundary
      (f := fun x => -f x) (f' := fun x => -f' x)
      (B := fun x => -f a + C * (x - a)) (B' := fun _ => C) ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      exact ((hf x hx).continuousAt.neg).continuousWithinAt
    · intro x hx
      exact (hf x (Set.Ico_subset_Icc_self hx)).neg.hasDerivWithinAt
    · simp
    · fun_prop
    · intro x hx
      have h := (((hasDerivWithinAt_id x (Set.Ici x)).sub_const a).const_mul C).const_add (-f a)
      simpa using h
    · intro x hx
      have := hC x (Set.Ico_subset_Icc_self hx)
      linarith
  have hb := key b (Set.right_mem_Icc.mpr hab)
  linarith

end Work.Diff.L
