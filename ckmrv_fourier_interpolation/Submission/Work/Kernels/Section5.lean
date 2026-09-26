/-
# Section 5: from the kernel equations to the hypotheses of Theorem 3.1

This file formalizes the algebraic content of CKMRV Corollary 5.2 (`corin4.1`): the
functional equations of `F = F₁ + F₂` and of `F̃ = -F₂|^τ_{d/2}S` follow from the two
equations satisfied by the kernel transform

  `F₂(τ,r) = 4 sin²(πr²/2) ∫_0^∞ K(τ,it) e^{-πr²t} dt`,

namely `F₂ |^τ_{d/2} (T-I)² = -F₁ |^τ_{d/2} (T-I)²` and `F₂ |^τ_{d/2} S (T-I)² = 0`, together
with the definitional relation `K̂ = -K |^τ_{d/2} S` (Theorem 4.9).

Everything here is algebra plus the definition of the (total, Bochner) integral: no
convergence, holomorphy or growth statement is used.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelEquations
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.KernelSlash
import Submission.Work.Kernels.Theorem31

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix MeasureTheory
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-! ## `T2op` in group-algebra form -/

lemma T2op_add' {F G : ℍ → ℂ} : T2op (fun τ => F τ + G τ) = T2op F + T2op G := by
  ext τ
  simp only [T2op, Pi.add_apply]
  ring

lemma T2op_neg' {F : ℍ → ℂ} : T2op (fun τ => -F τ) = - T2op F := by
  ext τ
  simp only [T2op, Pi.neg_apply]
  ring

/-- `T2op (X ∣[k] S) = slash k (S (T-I)²) X`: the second functional equation in group-algebra
form. -/
lemma T2op_slash_S (k : ℤ) (X : ℍ → ℂ) :
    T2op (X ∣[k] ModularGroup.S) = slash k (R_S * (R_T - 1) ^ 2) X := by
  rw [AlgebraFacts.slash_mul, slash_R_S, ← slash_T2]

/-! ## The functional equations of `F₂` imply those of `F` -/

/-- Corollary 5.2, first equation: if `F₂ |^τ_{d/2}(T-I)² = -F₁ |^τ_{d/2}(T-I)²`, then
`F = F₁ + F₂` satisfies `F(τ+2) - 2F(τ+1) + F(τ) = 0`. -/
theorem Fgen_T2 {K : ℍ → ℍ → ℂ}
    (h : ∀ r : ℝ, T2op (fun τ : ℍ => kernelTransform K τ r)
      = - T2op (fun τ : ℍ => gaussTerm τ r)) :
    ∀ r : ℝ, T2op (fun τ : ℍ => Fgen K τ r) = 0 := by
  intro r
  have hh := h r
  have : (fun τ : ℍ => Fgen K τ r)
      = fun τ => gaussTerm τ r + kernelTransform K τ r := by
    funext τ; simp [Fgen]
  rw [this, T2op_add', hh]
  simp

end Work.Kernels
