/-
# Auxiliary definitions for the growth propagation of the functional equations

This file sets up the two quantitative notions used in the proof of CKMRV
Proposition 3.2(2) (`Work.Asymptotics.bound_of_propagates`):

* `Work.Asymptotics.Frob` : the Frobenius norm of a matrix in `SL(2,ℤ)`,
  `‖γ‖² = a² + b² + c² + d²`.  It is the norm in which the linear dependence of the
  "carries" on the reduction element `γ` is naturally expressed.

* `Work.Asymptotics.coeffNorm` : the `ℓ¹`-norm `∑_δ ‖c_δ‖` of an element of the group algebra
  `R = ℂ[SL(2,ℤ)]`, together with `Work.Asymptotics.supportFrobLe`, the statement that every
  group element occurring in the support of a group-algebra element has Frobenius norm at most
  a given bound.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Residues.IdealImRowDiffAll

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The **Frobenius norm** of `γ ∈ SL(2,ℤ)`, `√(a² + b² + c² + d²)`.  All the growth bounds
for the propagation are polynomial in this quantity. -/
def Frob (γ : SL(2,ℤ)) : ℝ :=
  Real.sqrt (((γ 0 0 : ℤ) : ℝ) ^ 2 + ((γ 0 1 : ℤ) : ℝ) ^ 2 +
    ((γ 1 0 : ℤ) : ℝ) ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2)

lemma Frob_nonneg (γ : SL(2,ℤ)) : 0 ≤ Frob γ := Real.sqrt_nonneg _

lemma one_le_one_add_Frob (γ : SL(2,ℤ)) : 1 ≤ 1 + Frob γ := by
  have := Frob_nonneg γ; linarith

/-- The `ℓ¹`-norm of a group algebra element: the sum of the absolute values of its
coefficients. -/
def coeffNorm (x : R) : ℝ := ∑ γ ∈ x.coeff.support, ‖x.coeff γ‖

lemma coeffNorm_nonneg (x : R) : 0 ≤ coeffNorm x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- `supportFrobLe x K` says: every group element occurring in the support of the group
algebra element `x` has Frobenius norm at most `K`. -/
def supportFrobLe (x : R) (K : ℝ) : Prop := ∀ γ ∈ x.coeff.support, Frob γ ≤ K

end Work.Asymptotics

namespace Work.Asymptotics

/-- The Möbius action of `SL(2,ℤ)` on `ℍ`, written out as a plain function so that it can be
used in statements that do not `open scoped MatrixGroups`. -/
def slSmul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ) : ℍ := γ • τ

@[simp] lemma slSmul_apply (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ) :
    slSmul γ τ = γ • τ := rfl

end Work.Asymptotics
