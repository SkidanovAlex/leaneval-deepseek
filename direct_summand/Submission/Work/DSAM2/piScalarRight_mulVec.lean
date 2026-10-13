import Mathlib

namespace Work.DSAM2

/-- Naturality of the coordinate isomorphism `TensorProduct.piScalarRight B B' B' ι : B' ⊗[B] (ι → B) ≃ₗ[B'] (ι → B')`
with the linear map attached to a matrix: base change of `M.mulVecLin` is `Matrix.mulVec` for the entrywise-extended
matrix.  This is the transport that lets `Matrix.mulVec` solvability be tested after base change. -/
theorem piScalarRight_mulVec {B : Type*} [CommRing B] {B' : Type*} [CommRing B']
    [Algebra B B'] {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (M : Matrix κ ι B) (x' : TensorProduct B B' (ι → B)) :
    TensorProduct.piScalarRight B B' B' κ ((M.mulVecLin.lTensor B') x') =
      (M.map (algebraMap B B')).mulVec (TensorProduct.piScalarRight B B' B' ι x') := by
  -- Work with `mulVecLin` on the right-hand side so that additivity is available.
  have key : ∀ (z : TensorProduct B B' (ι → B)),
      (TensorProduct.piScalarRight B B' B' κ) ((M.mulVecLin.lTensor B') z) =
      (M.map (algebraMap B B')).mulVecLin ((TensorProduct.piScalarRight B B' B' ι) z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul y f =>
        -- On a pure tensor both sides reduce to explicit coordinate formulas.
        simp only [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply,
          TensorProduct.piScalarRightHom_tmul]
        ext i
        simp only [Algebra.smul_def, Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum,
          Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, mul_assoc]
    | add a b ha hb => simp only [map_add, ha, hb]
  exact key x'

end Work.DSAM2
