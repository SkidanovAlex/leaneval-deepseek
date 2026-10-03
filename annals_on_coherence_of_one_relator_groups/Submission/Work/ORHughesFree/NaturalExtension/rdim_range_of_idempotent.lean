import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

/-- The rows of the matrix `M = Matrix.toLinearMapRight'.symm e` of an endomorphism `e` of `R^n`
are the images of the standard basis vectors of `R^n` under `e`.  Indeed
`Matrix.toLinearMapRight' M` acts by `x ↦ x ᵥ* M`, and `Pi.single i 1 ᵥ* M = M.row i`. -/
theorem rows_toLinearMapRight'_symm {R : Type u} [Ring R] {n : ℕ}
    (e : Module.End R (Fin n → R)) :
    (fun i : Fin n => e (Pi.single i (1 : R))) =
      (fun i : Fin n => fun j : Fin n => (Matrix.toLinearMapRight'.symm e) i j) := by
  funext i
  set M : Matrix (Fin n) (Fin n) R := Matrix.toLinearMapRight'.symm e with hM
  have hMe : Matrix.toLinearMapRight' M = e := LinearEquiv.apply_symm_apply Matrix.toLinearMapRight' e
  rw [← hMe, Matrix.toLinearMapRight'_apply, Matrix.single_vecMul, Matrix.row]
  simp

/-- The range of an endomorphism `e` of the free module `R^n` is spanned by the images of the
standard basis vectors. -/
theorem range_eq_span_basis_image {R : Type u} [Ring R] {n : ℕ}
    (e : Module.End R (Fin n → R)) :
    LinearMap.range e =
      Submodule.span R (Set.range (fun i : Fin n => e (Pi.single i (1 : R)))) := by
  have hbasis : Set.range (Pi.basisFun R (Fin n)) =
      Set.range (fun i : Fin n => (Pi.single i (1 : R) : Fin n → R)) := by
    congr 1 with i; rw [Pi.basisFun_apply]
  calc LinearMap.range e = Submodule.map e ⊤ := (Submodule.map_top e).symm
    _ = Submodule.map e (Submodule.span R (Set.range (Pi.basisFun R (Fin n)))) := by
          rw [(Pi.basisFun R (Fin n)).span_eq]
    _ = Submodule.span R (e '' Set.range (Pi.basisFun R (Fin n))) :=
          Submodule.map_span e (Set.range (Pi.basisFun R (Fin n)))
    _ = Submodule.span R (e '' Set.range (fun i : Fin n => (Pi.single i (1 : R) : Fin n → R))) := by
          rw [hbasis]
    _ = Submodule.span R (Set.range (fun i : Fin n => e (Pi.single i (1 : R)))) := by
          rw [← Set.range_comp]; rfl

/-- For an endomorphism `e` of the free module `R^n` over a von Neumann regular ring `R`, the row
dimension `rdim rk (range e)` of its range equals the Sylvester rank of its matrix
`Matrix.toLinearMapRight'.symm e`.

The range of `e` is the span of the images `e (Pi.single i 1)` of the standard basis vectors, and
these are exactly the rows of the matrix of `e`; so both sides are `rdim` of the row span of that
matrix, computed by `rdim_eq_rk_rows`.  (The idempotency hypothesis `he` is not needed for the
identity itself.) -/
theorem rdim_range_of_idempotent {R : Type u} [Ring R] [VonNeumannRegularRing R]
    (rk : SylvesterRank R) {n : ℕ} (e : Module.End R (Fin n → R)) (he : e * e = e) :
    rdim rk (LinearMap.range e) = rk.rk n n (Matrix.toLinearMapRight'.symm e) := by
  rw [range_eq_span_basis_image e, rows_toLinearMapRight'_symm e, rdim_eq_rk_rows]

end Work.ORHughesFree.NaturalExtension
