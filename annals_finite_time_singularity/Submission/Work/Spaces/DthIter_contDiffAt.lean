/-
Copyright: work module for the Elgindi finite-time singularity project.

# `D_θ` preserves `C^∞`-regularity at a point

The operator `D_θ f = sin(2θ) ∂_θ f` of `Submission.Work.Spaces.Defs` sends
functions that are `C^∞` at a point `(z,θ)` to functions that are `C^∞` at the
same point, and hence so does every iterate `DthIter j`.  The key input is
`contDiffAt_deriv_slice` of `Submission.Work.Spaces.pz_aux`, which says that the
`θ`-slice derivative of a `C^∞` function of two variables is again `C^∞`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- `D_θ` preserves `C^∞`-regularity at a point. -/
theorem Dth_contDiffAt {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hg : ContDiffAt ℝ ⊤ (Function.uncurry g) (z, θ)) :
    ContDiffAt ℝ ⊤ (Function.uncurry (Dth g)) (z, θ) := by
  have h1 : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (z, θ) := by
    fun_prop
  have h2 := contDiffAt_deriv_slice hg
  exact h1.mul h2

/-- Every iterate of `D_θ` preserves `C^∞`-regularity at a point. -/
theorem DthIter_contDiffAt (f : ℝ → ℝ → ℝ) (j : ℕ) {z θ : ℝ}
    (h : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter j f)) (z, θ) := by
  induction j with
  | zero => simpa using h
  | succ n ih => simpa using Dth_contDiffAt ih

end Work.Spaces
