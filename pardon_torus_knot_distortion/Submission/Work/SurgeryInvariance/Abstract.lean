import Submission.Work.SurgeryInvariance.Defs

/-!
# A locally constant quantity on the parameter line is constant

Pardon's argument shows that the invariant attached to the region `F ∩ int(S_t)` does not change
while the sphere family is deformed without surgery, and that a single `2`-surgery changes it by
"at most a disc"; its values therefore sit in a set with no room for a jump.  The abstract
content of the last step is that a quantity on the connected parameter line `ℝ` which is constant
on a neighbourhood of every parameter is constant everywhere.

This file proves that step in the form used by `Work.SurgeryInvariance.Core`, for an arbitrary
target type (in the application, the target is the lattice of `ℚ`-subspaces `WindingSpan P (A t)`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance

noncomputable section

/-- **A locally constant quantity on `ℝ` is constant.**  If at every parameter `t` the value of
`f` on a small ball around `t` is constant, then `f` takes the same value at any two parameters.
No hypothesis on the set of exceptional parameters is needed: the local constancy has to be
supplied at *every* point, including them. -/
theorem eq_of_locally_const {α : Type*} {f : ℝ → α}
    (h : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε → f s = f t) (x y : ℝ) : f x = f y := by
  have hlc : IsLocallyConstant f := by
    intro s
    rw [Metric.isOpen_iff]
    intro t ht
    obtain ⟨ε, hε, hc⟩ := h t
    refine ⟨ε, hε, fun u hu => ?_⟩
    have hu' : |u - t| < ε := by simpa [Real.dist_eq] using hu
    show f u ∈ s
    rw [hc u hu']
    exact ht
  exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ x) (mem_univ y)

end

end Work.SurgeryInvariance
