import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.SkeletonDefs
import Submission.Work.DeltaHomology.Skeleton

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.DeltaHomology

/-- The defining equation of `skelHomOfLe` in the non-vacuous case: for `j ≤ n`
the inclusion `n`-skeleton → `m`-skeleton is the identity on `j`-simplices, up
to the canonical identifications `skelCard K n j = K.card j = skelCard K m j`. -/
theorem skelHomOfLe_eq (K : DeltaCx) {n m : ℕ} (h : n ≤ m) {j : ℕ} (hj : j ≤ n)
    (σ : Fin (skelCard K n j)) :
    skelHomOfLe K h σ
      = Fin.cast (by rw [skelCard_eq K hj, skelCard_eq K (by omega)]) σ := by
  rw [skelHomOfLe, dif_pos hj]

/-- The inclusions between skeleta commute with faces: for `n ≤ m` the map
`skelHomOfLe K h : Fin (skelCard K n j) → Fin (skelCard K m j)` (the identity on
`j`-simplices, which are the same for `j ≤ n` and empty above) is compatible with
`skelFace`, so that `skelHomOfLe K h` is the underlying map of a simplicial map
`K.skel n ⟶ K.skel m` of `Δ`-complexes.

Cases: if `j + 1 ≤ n` then both `skelHomOfLe` and `skelFace` are the identity/`K.face`
up to casts (use `skelFace_eq`, `skelHomOfLe` and `Fin.ext`), otherwise
`σ : Fin (skelCard K n (j+1)) = Fin 0` and one eliminates. -/
theorem skelHomOfLe_face (K : DeltaCx) {n m : ℕ} (h : n ≤ m) {j : ℕ}
    (σ : Fin (skelCard K n (j + 1))) (i : Fin (j + 2)) :
    skelHomOfLe K h (skelFace K n σ i) = skelFace K m (skelHomOfLe K h σ) i := by
  by_cases hj : j + 1 ≤ n
  · -- Non-vacuous case: both sides are `K.face` of `Fin.cast _ σ` behind casts.
    have hjn : j ≤ n := by omega
    rw [skelFace_eq K n hj, skelFace_eq K m (by omega)]
    rw [skelHomOfLe_eq K h hjn, skelHomOfLe_eq K h hj]
    rw [Fin.cast_cast]
    apply Fin.ext
    simp only [Fin.val_cast]
    congr 1
  · -- Vacuous case: `skelCard K n (j+1) = 0`, so `σ` is an element of `Fin 0`.
    exact Fin.elim0 (Fin.cast (by rw [skelCard_eq_zero K (by omega)]) σ)

end Work.DeltaHomology
