import Mathlib

namespace Work.OddExistence.Estimates

/-- On a compact interval `[c, M]` with `c > 0`, the map `x ↦ x ^ r` (real power) is
Lipschitz.  The Lipschitz constant produced here is
`|r| * max (c ^ (r - 1)) (M ^ (r - 1))`, which bounds `‖deriv (x ↦ x ^ r) x‖ = |r| x ^ (r - 1)`
uniformly on `[c, M]`. -/
theorem rpow_lipschitz_Icc {r c M : ℝ} (hc : 0 < c) (hcM : c ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Set.Icc c M, ∀ y ∈ Set.Icc c M,
      |x ^ r - y ^ r| ≤ L * |x - y| := by
  have _ : c ≤ M := hcM
  refine ⟨|r| * max (c ^ (r - 1)) (M ^ (r - 1)), by positivity, ?_⟩
  -- `|r| * max (c ^ (r - 1)) (M ^ (r - 1))` bounds the derivative of `x ↦ x ^ r` on `[c, M]`
  have hbound : ∀ t ∈ Set.Icc c M,
      ‖r * t ^ (r - 1)‖ ≤ |r| * max (c ^ (r - 1)) (M ^ (r - 1)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hc ht.1
    have hpos : 0 < t ^ (r - 1) := Real.rpow_pos_of_pos ht0 _
    have hexp : t ^ (r - 1) ≤ max (c ^ (r - 1)) (M ^ (r - 1)) := by
      rcases lt_or_ge (r - 1) 0 with h | h
      · exact le_trans (Real.rpow_le_rpow_of_nonpos hc ht.1 h.le) (le_max_left _ _)
      · exact le_trans (Real.rpow_le_rpow ht0.le ht.2 h) (le_max_right _ _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_left hexp (abs_nonneg r)
  intro x hx y hy
  -- mean value theorem on the convex set `[c, M]`
  have hLip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => t ^ r) (f' := fun t : ℝ => r * t ^ (r - 1)) (s := Set.Icc c M)
    (fun t ht => (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le hc ht.1)))).hasDerivWithinAt)
    hbound (convex_Icc c M) hx hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (y ^ r) (x ^ r), abs_sub_comm y x] at hLip
  exact hLip

end Work.OddExistence.Estimates
