import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.poisson

/-!
# The Poisson bound for formal solutions (AJ §9)

`poisson` (sibling module `Basic.poisson`) is the exact Poisson formula for a formal solution
`u` of `H u = E u` and an interval `[x₁,x₂]` with invertible Dirichlet restriction:

`u y = - G_{[x₁,x₂]}(y,x₁) u(x₁-1) - G_{[x₁,x₂]}(y,x₂) u(x₂+1)`   (`x₁ ≤ y ≤ x₂`).

Taking norms and using the triangle inequality (and multiplicativity of the norm) turns the
equality into the bound used by the singularity-of-a-zero argument and the patching scheme.
-/

namespace Work.TMC16Core.Basic

theorem poisson_bound {α lam θ : ℝ} {E : ℂ} {u : ℤ → ℂ}
    (hsol : Work.TMC16Core.IsFormalSol α lam θ E u) {x₁ x₂ y : ℤ}
    (hdet : (Work.TMC16Core.dirMat α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat)).det ≠ 0)
    (h1 : x₁ ≤ y) (h2 : y ≤ x₂) :
    ‖u y‖ ≤ ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₁‖ * ‖u (x₁ - 1)‖ +
              ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₂‖ * ‖u (x₂ + 1)‖ := by
  have h := poisson α lam θ E x₁ x₂ y u hsol hdet h1 h2
  calc ‖u y‖ =
        ‖-(Work.TMC16Core.G α lam θ E x₁ x₂ y x₁) * u (x₁ - 1) -
          (Work.TMC16Core.G α lam θ E x₁ x₂ y x₂) * u (x₂ + 1)‖ := by rw [h]
    _ ≤ ‖-(Work.TMC16Core.G α lam θ E x₁ x₂ y x₁) * u (x₁ - 1)‖ +
          ‖(Work.TMC16Core.G α lam θ E x₁ x₂ y x₂) * u (x₂ + 1)‖ := norm_sub_le _ _
    _ = ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₁‖ * ‖u (x₁ - 1)‖ +
          ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₂‖ * ‖u (x₂ + 1)‖ := by
        simp only [norm_mul, norm_neg]

end Work.TMC16Core.Basic
