import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

lemma exp_weighted_monotone {g g' : ℝ → ℝ} {c T : ℝ}
    (hcont : ContinuousOn g (Set.Icc 0 T))
    (hder : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt g (g' s) s)
    (hge : ∀ s ∈ Set.Ioo (0 : ℝ) T, 0 ≤ c * g s + g' s) :
    MonotoneOn (fun s : ℝ => Real.exp (c * s) * g s) (Set.Icc 0 T) := by
  -- The derivative of `s ↦ exp (c * s) * g s` on the interior is
  -- `exp (c * s) * (c * g s + g' s)`, which is nonnegative by `hge`.
  have hderF : ∀ x ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => Real.exp (c * s) * g s)
        (Real.exp (c * x) * (c * g x + g' x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (c * s)) (Real.exp (c * x) * c) x :=
      (Real.hasDerivAt_exp (c * x)).comp x (hasDerivAt_const_mul (x := x) c)
    have h2 := h1.mul (hder x hx)
    convert h2 using 1
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) T)
  · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)).mul
      hcont
  · intro x hx
    rw [interior_Icc] at hx
    exact (hderF x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hderF x hx).deriv]
    exact mul_nonneg (Real.exp_pos _).le (hge x hx)

end Work.Diff.EXT
