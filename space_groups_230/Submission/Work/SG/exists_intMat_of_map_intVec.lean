import Mathlib
import Submission.Work.SG.Defs

/-!
# Linear maps of `ℝ³` preserving `ℤ³` are given by integer matrices

If an `ℝ`-linear map `f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)` carries every integer vector
`intVec n` (`n : Fin 3 → ℤ`) to an integer vector, then its matrix in the standard basis has
integer entries; moreover the whole map is `Matrix.toLin'` of that integer matrix (cast to `ℝ`)
and the action on lattice vectors is `n ↦ A.mulVec n`.

The proof is one line of bookkeeping: the hypothesis applied to the standard basis vector
`Pi.single j 1` says that the `j`-th column of the matrix of `f` is integral, and the standard
basis spans.
-/

namespace Work.SG

theorem exists_intMat_of_map_intVec (f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hf : ∀ n : Fin 3 → ℤ, ∃ m : Fin 3 → ℤ, f (Work.SG.intVec n) = Work.SG.intVec m) :
    ∃ A : Work.SG.IMat, (∀ n : Fin 3 → ℤ, f (Work.SG.intVec n) = Work.SG.intVec (A.mulVec n)) ∧
      f = Matrix.toLin' (A.map (Int.cast : ℤ → ℝ)) := by
  classical
  -- The standard basis vectors of `ℝ³` are the integer vectors `Pi.single j 1`.
  have hsingle : ∀ j : Fin 3, intVec (Pi.single j (1 : ℤ)) = Pi.single j (1 : ℝ) := by
    intro j; ext i; simp [intVec, Pi.single_apply]
  -- The matrix whose `j`-th column is the (integral) image of the `j`-th basis vector.
  let A : IMat := Matrix.of fun i j => Classical.choose (hf (Pi.single j (1 : ℤ))) i
  have hA : ∀ j : Fin 3, f (Pi.single j (1 : ℝ)) = fun i => (A i j : ℝ) := by
    intro j
    have h := Classical.choose_spec (hf (Pi.single j (1 : ℤ)))
    have h' : f (Pi.single j (1 : ℝ))
        = intVec (Classical.choose (hf (Pi.single j (1 : ℤ)))) := by
      rw [← hsingle j]; exact h
    rw [h']
    ext i
    simp [A, intVec]
  -- Casting the integer matrix to `ℝ` and multiplying by `intVec n` gives `intVec (A.mulVec n)`.
  have hcast : ∀ n : Fin 3 → ℤ,
      (A.map (Int.cast : ℤ → ℝ)).mulVec (intVec n) = intVec (A.mulVec n) := by
    intro n; ext i
    simp only [Matrix.mulVec, dotProduct, intVec, Matrix.map_apply]
    push_cast
    rfl
  -- Identifying the matrix of `f` in the standard basis.
  have hmat : LinearMap.toMatrix' f = A.map (Int.cast : ℤ → ℝ) := by
    ext i j
    rw [LinearMap.toMatrix'_apply, Matrix.map_apply]
    simpa using congrFun (hA j) i
  have hfl : f = Matrix.toLin' (A.map (Int.cast : ℤ → ℝ)) := by
    rw [← hmat, Matrix.toLin'_toMatrix']
  refine ⟨A, fun n => ?_, hfl⟩
  rw [hfl, Matrix.toLin'_apply, hcast]

end Work.SG
