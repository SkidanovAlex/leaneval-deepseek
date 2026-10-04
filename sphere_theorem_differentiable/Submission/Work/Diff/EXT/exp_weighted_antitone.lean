import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- **Exponential-weighted monotonicity (Gronwall-type).**

If `g` is continuous on `[0,T]`, differentiable on `(0,T)` with derivative `g'`, and
`c * g s + g' s ≤ 0` on `(0,T)`, then `s ↦ exp (c*s) * g s` is antitone on `[0,T]`.

Indeed the derivative of `s ↦ exp (c*s) * g s` is `exp (c*s) * (c * g s + g' s) ≤ 0`. -/
lemma exp_weighted_antitone {g g' : ℝ → ℝ} {c T : ℝ}
    (hcont : ContinuousOn g (Set.Icc 0 T))
    (hder : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt g (g' s) s)
    (hle : ∀ s ∈ Set.Ioo (0 : ℝ) T, c * g s + g' s ≤ 0) :
    AntitoneOn (fun s : ℝ => Real.exp (c * s) * g s) (Set.Icc 0 T) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
  · exact (by fun_prop : Continuous fun s : ℝ => Real.exp (c * s)).continuousOn.mul hcont
  · intro x hx
    rw [interior_Icc] at hx
    have hd : HasDerivAt g (g' x) x := hder x hx
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (c * s)) (Real.exp (c * x) * c) x := by
      simpa using ((hasDerivAt_id x).const_mul c).exp
    have h2 := h1.mul hd
    have h2' : HasDerivAt (fun s : ℝ => Real.exp (c * s) * g s)
        (Real.exp (c * x) * (c * g x + g' x)) x := by
      convert h2 using 1
      ring
    exact h2'.hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hle x hx)

end Work.Diff.EXT
