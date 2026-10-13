import Submission.Work.DSAM2.Basic
import Submission.Work.DSAM2.exists_eq_of_lTensor_eq
import Submission.Work.DSAM2.piScalarRight_mulVec

/-!
# DSAM2: faithful-flat descent for linear systems

The classical obstruction computation behind `DSMap.Mix.modSplit_descent`: the solvability of an
inhomogeneous linear system over a ring `B` is detected after base change to a faithfully flat
`B`-algebra `B'`.  The proof combines

* `Work.DSAM2.exists_eq_of_lTensor_eq`: solvability of `L v = y` descends along a faithfully flat
  extension (via the cokernel of `L` and `Module.FaithfullyFlat.tensorProduct_mk_injective`);
* `Work.DSAM2.piScalarRight_mulVec` and `Work.DSAM2.piScalarRight_tmul_one`: the transport, under
  Mathlib's coordinate isomorphism `TensorProduct.piScalarRight B B' B' ι`, between the base change
  `B' ⊗[B] (ι → B)` of a matrix equation and the entrywise-extended matrix equation over `B'`.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Work.DSAM2

universe u

/-- Solvability of the matrix equation `M.mulVec q = y` descends along a faithfully flat algebra
extension: it is equivalent to the solvability of the entrywise-extended equation over `B'`.

This is the algebraic core of the almost-splitting descent `DSMap.Mix.modSplit_descent`. -/
theorem exists_mulVec_iff_of_faithfullyFlat {B : Type*} [CommRing B] {B' : Type*} [CommRing B']
    [Algebra B B'] [Module.FaithfullyFlat B B'] {κ ι : Type*} [Fintype κ] [Fintype ι]
    (M : Matrix κ ι B) (y : κ → B) :
    (∃ q : ι → B, M.mulVec q = y) ↔
      (∃ q' : ι → B', (M.map (algebraMap B B')).mulVec q' = fun k => algebraMap B B' (y k)) := by
  classical
  -- The two forms of the right-hand side are matched by the coordinate isomorphism.
  have key : ∀ x' : TensorProduct B B' (ι → B),
      ((M.mulVecLin.lTensor B') x' = (1 : B') ⊗ₜ[B] y) ↔
      ((M.map (algebraMap B B')).mulVec (TensorProduct.piScalarRight B B' B' ι x') =
        fun k => algebraMap B B' (y k)) := by
    intro x'
    constructor
    · intro hx
      have h := congrArg (TensorProduct.piScalarRight B B' B' κ) hx
      rw [piScalarRight_mulVec M x', piScalarRight_tmul_one y] at h
      exact h
    · intro hy
      refine (TensorProduct.piScalarRight B B' B' κ).injective ?_
      rw [piScalarRight_mulVec M x', piScalarRight_tmul_one y]
      exact hy
  have hiff := exists_eq_of_lTensor_eq (B := B) (B' := B') M.mulVecLin y
  constructor
  · rintro ⟨q, hq⟩
    have h2 : (M.mulVecLin.lTensor B') ((1 : B') ⊗ₜ[B] q) = (1 : B') ⊗ₜ[B] y := by
      rw [LinearMap.lTensor_tmul]
      exact congrArg (fun z => (1 : B') ⊗ₜ[B] z) (by simpa [Matrix.mulVecLin_apply] using hq)
    have h3 := (key _).mp h2
    rw [piScalarRight_tmul_one q] at h3
    exact ⟨fun i => algebraMap B B' (q i), h3⟩
  · rintro ⟨q', hq'⟩
    have hb : ∃ v' : TensorProduct B B' (ι → B),
        (M.mulVecLin.lTensor B') v' = (1 : B') ⊗ₜ[B] y :=
      ⟨(TensorProduct.piScalarRight B B' B' ι).symm q', (key _).mpr (by simpa using hq')⟩
    obtain ⟨q, hq⟩ := hiff.mpr hb
    exact ⟨q, by simpa [Matrix.mulVecLin_apply] using hq⟩

end Work.DSAM2
