import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper

namespace Work.Mostow

open Submission.Mostow

/-- Decomposition of the hyperboloid lift `hlift u` along the null direction `theta ξ`:
`hlift u = ⟪u,ξ⟫ • θ_ξ + (tpart u − ⟪u,ξ⟫) • hlift 0 + wvec (u − ⟪u,ξ⟫ • ξ)`. -/
theorem hliftDecomp {n : ℕ} (ξ u : Submission.Mostow.E n) :
    Submission.Mostow.hlift u = (inner ℝ u ξ) • Work.Mostow.theta ξ
      + (Submission.Mostow.tpart u - inner ℝ u ξ) • Submission.Mostow.hlift (0 : Submission.Mostow.E n)
      + Work.Mostow.wvec (u - (inner ℝ u ξ) • ξ) := by
  ext a
  rcases a with i | j
  · simp [Work.Mostow.theta, Submission.Mostow.hlift, Work.Mostow.wvec, Pi.add_apply,
      Pi.smul_apply]
  · fin_cases j
    simp [Work.Mostow.theta, Submission.Mostow.hlift, Work.Mostow.wvec, Submission.Mostow.tpart,
      Pi.add_apply, Pi.smul_apply]

end Work.Mostow
