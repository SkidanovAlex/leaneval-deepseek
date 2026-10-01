import Mathlib
import Submission.Work.LinnikContract.Defs

open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas

/-- The `T = 0` Hadamard partial-fraction kernel `Re (1/(σ₁ - u) - 1/((-1) - u))`, written in
real coordinates.  For a real `β` it equals `1/(σ₁ - β) + 1/(1 + β)`. -/
def realKernel (σ₁ : ℝ) (u : ℂ) : ℝ :=
  (σ₁ - u.re) / ((σ₁ - u.re) ^ 2 + u.im ^ 2)
    + (1 + u.re) / ((1 + u.re) ^ 2 + u.im ^ 2)

/-- The multiplicity-weighted number of real zeros `β` of a Dirichlet character with
`λ(β) = (1 - β) log q ≤ t`. -/
def realZeroCountFinsum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ∑ᶠ β : ℝ, if Work.LinnikContract.zeroMult χ ((β : ℂ)) ≠ 0 ∧
      Work.LinnikContract.lamOf q ((β : ℂ)) ≤ t
    then (Work.LinnikContract.zeroMult χ ((β : ℂ)) : ℝ) else 0

/-- The divisor-weighted Hadamard kernel of the completed `L`-function of the primitive
character inducing `χ`, summed over the ball of radius `1` about the origin. -/
def divisorKernelFinsum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ₁ : ℝ) : ℝ :=
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  ∑ᶠ u : ℂ, (((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0 : ℂ) 1)) u : ℤ) : ℝ) * realKernel σ₁ u

/-- At a real point the kernel is `1/(σ₁ - β) + 1/(1 + β)`. -/
lemma realKernel_ofReal (σ₁ β : ℝ) :
    realKernel σ₁ (β : ℂ) = 1 / (σ₁ - β) + 1 / (1 + β) := by
  have key : ∀ a : ℝ, a / a ^ 2 = 1 / a := by
    intro a
    rcases eq_or_ne a 0 with h | h
    · rw [h]; norm_num
    · field_simp
  rw [realKernel]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, add_zero]
  rw [key (σ₁ - β), key (1 + β)]

end Work.LinnikAreas
