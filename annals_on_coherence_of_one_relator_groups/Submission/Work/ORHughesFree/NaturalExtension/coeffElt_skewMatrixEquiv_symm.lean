import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.ampDefs

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The inverse of the entrywise isomorphism `skewMatrixEquiv` is "coefficientwise": the `k`-th
coefficient (in `M_N(R)[t^{±1};τ]`) of the preimage of a matrix `A` over `R[t^{±1};τ]` is the
matrix of `k`-th coefficients of `A`.  This is `skewMatrixToHom_coeff` read backwards along the
isomorphism. -/
theorem coeffElt_skewMatrixEquiv_symm {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (N : ℕ) (A : Matrix (Fin N) (Fin N) (Work.ORHughesFree.NaturalExtension.SkewL R)) (k : ℤ) :
    Work.ORHughesFree.NaturalExtension.coeffElt
        ((Work.ORHughesFree.NaturalExtension.skewMatrixEquiv R N).symm A) k
      = Work.ORHughesFree.NaturalExtension.coeffMat A k := by
  ext i j
  -- `skewMatrixEquiv` is (definitionally) `skewMatrixToHom`, so its inverse is a preimage.
  have h : skewMatrixToHom R N ((skewMatrixEquiv R N).symm A) = A := by
    rw [← skewMatrixEquiv_apply R N]
    exact (skewMatrixEquiv R N).apply_symm_apply A
  -- Compare `(i,j)` entries of coefficients along `h`.
  have hc := congrArg (fun z : Matrix (Fin N) (Fin N) (SkewL R) =>
    (z i j).coeff (Multiplicative.ofAdd k)) h
  rw [skewMatrixToHom_coeff R N] at hc
  simpa [coeffElt, coeffMat] using hc

end Work.ORHughesFree.NaturalExtension
