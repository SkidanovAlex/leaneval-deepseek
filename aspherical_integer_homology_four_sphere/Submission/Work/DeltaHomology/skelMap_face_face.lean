import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.SkeletonDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.DeltaHomology

/-- The inclusion of the `n`-skeleton of a `Δ`-complex into the complex itself
commutes with the face maps: this is the `map_face` obligation for the simplicial
map `skelMap : (skel K n).Hom K` assembled in
`Submission/Work/DeltaHomology/Skeleton.lean`.

Cases: if `k+1 ≤ n` then `skelMap` and `skelFace` are `K.face`/the identity up to
casts (`skelMap_eq`, `skelFace_eq`), so both sides are `K.face` of cast-equal
arguments and `Fin.ext`/`Fin.val_cast` finish; if `¬ k+1 ≤ n` then
`σ : Fin (skelCard K n (k+1)) = Fin 0` and one eliminates. -/
theorem skelMap_face_face (K : DeltaCx) (n : ℕ) {k : ℕ} (σ : Fin (skelCard K n (k + 1)))
    (i : Fin (k + 2)) :
    skelMap K n (skelFace K n σ i) = K.face (skelMap K n σ) i := by
  by_cases h1 : k + 1 ≤ n
  · -- Non-vacuous case: unfold `skelFace` and `skelMap` into `K.face` behind
    -- `Fin.cast`s; the two casts surrounding `K.face` are inverse to one another
    -- and the inner casts of `skelFace_eq` and `skelMap_eq` coincide, so the
    -- identity is `rfl` after the cast bookkeeping.
    have hk : k ≤ n := by omega
    rw [skelFace_eq K n h1, skelMap_eq K n hk, skelMap_eq K n h1]
    rw [Fin.cast_cast, Fin.cast_eq_self]
  · -- Vacuous case: `skelCard K n (k+1) = 0`, so `σ` is an element of `Fin 0`.
    have hz : skelCard K n (k + 1) = 0 := skelCard_eq_zero K (by omega)
    exact Fin.elim0 (Fin.cast hz σ)

end Work.DeltaHomology
