import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.FP.PencilDefs

/-!
# `Work.KT.FP.SliceAux` — slices of a Laurent matrix over `C(X × [0,1], ℂ)`

The slice at `t` of a Laurent polynomial with coefficients in `C(X × [0,1], ℂ)` is the Laurent
polynomial over `C(X, ℂ)` obtained by evaluating every coefficient at `x ↦ (x,t)`
(`lapSlice`), and `matSlice` is its matrix version.  These are the objects in which the homotopy
invariance of `Work.KT.FP.lindAt` is phrased.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

/-- The slice `x ↦ (x,t)` of `X × [0,1]`. -/
def sliceCm (X : Type) [TopologicalSpace X] (t : unitInterval) : C(X, X × unitInterval) where
  toFun x := (x, t)
  continuous_toFun := continuous_id.prodMk continuous_const

/-- The slice `(x,z) ↦ ((x,t),z)` of `(X × [0,1]) × S¹`. -/
def sliceSphCm (X : Type) [TopologicalSpace X] (t : unitInterval) :
    C(X × Sph ℂ, (X × unitInterval) × Sph ℂ) where
  toFun p := ((p.1, t), p.2)
  continuous_toFun := (continuous_fst.prodMk continuous_const).prodMk continuous_snd

/-- Evaluation of a function on `X × [0,1]` at the slice `t`. -/
def sliceHom (X : Type) [TopologicalSpace X] (t : unitInterval) :
    C(X × unitInterval, ℂ) →+* C(X, ℂ) where
  toFun f := f.comp (sliceCm X t)
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl
  map_zero' := by ext x; rfl
  map_add' f g := by ext x; rfl

/-- The slice of a Laurent polynomial over `C(X × [0,1], ℂ)`. -/
def lapSlice (X : Type) [TopologicalSpace X] (t : unitInterval)
    (q : LaurentPolynomial C(X × unitInterval, ℂ)) : LaurentPolynomial C(X, ℂ) :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (sliceHom X t) (map_zero (sliceHom X t)) q.coeff)

/-- The slice of a Laurent matrix over `C(X × [0,1], ℂ)`. -/
def matSlice (X : Type) [TopologicalSpace X] (t : unitInterval) {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X × unitInterval, ℂ))) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)) :=
  Q.map (lapSlice X t)

end

end Work.KT.FP
