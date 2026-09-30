import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.SkeletonDefs
import Submission.Work.DeltaHomology.skelCard_eq_zero_of_lt
import Submission.Work.DeltaHomology.skelFace_face_face
import Submission.Work.DeltaHomology.skelMap_face_face

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Skeleta of a `Δ`-complex

The `n`-skeleton `K.skel n` of a finite `Δ`-complex `K` is the truncation to
simplices of dimension `≤ n`: a `DeltaCx` with `card j = if j ≤ n then K.card j
else 0`, faces restricted (`skelCard`/`skelFace` in
`Submission/Work/DeltaHomology/SkeletonDefs.lean`), plus the inclusion
`K.skelHom n : K.skel n ⟶ K` of `Δ`-complexes.

These are the input to the skeleta induction of Hatcher's theorem
(`deltaChainMap_quasiIso`); see `Submission/Work/DeltaHomology/NOTES.md`, §4.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

/-- The `n`-skeleton of a `Δ`-complex: the subcomplex of simplices of dimension
`≤ n`. -/
def DeltaCx.skel (K : DeltaCx) (n : ℕ) : DeltaCx where
  dim := min K.dim n
  card := skelCard K n
  face := skelFace K n
  face_face := skelFace_face_face K n
  card_eq_zero := fun k hk => skelCard_eq_zero_of_lt K n hk

@[simp]
theorem DeltaCx.skel_dim (K : DeltaCx) (n : ℕ) : (K.skel n).dim = min K.dim n := rfl

@[simp]
theorem DeltaCx.skel_card (K : DeltaCx) (n j : ℕ) : (K.skel n).card j = skelCard K n j := rfl

/-- The `j`-simplices of the `n`-skeleton are the `j`-simplices of `K` when
`j ≤ n`. -/
theorem DeltaCx.skel_card_eq (K : DeltaCx) (n : ℕ) {j : ℕ} (h : j ≤ n) :
    (K.skel n).card j = K.card j := skelCard_eq K h

/-- There are no `j`-simplices in the `n`-skeleton when `j > n`. -/
theorem DeltaCx.skel_card_eq_zero (K : DeltaCx) (n : ℕ) {j : ℕ} (h : n < j) :
    (K.skel n).card j = 0 := skelCard_eq_zero K h

/-- The face of a simplex in the skeleton, in the non-vacuous case. -/
theorem DeltaCx.skel_face_eq (K : DeltaCx) (n : ℕ) {j : ℕ} (h : j + 1 ≤ n)
    (σ : Fin ((K.skel n).card (j + 1))) (i : Fin (j + 2)) :
    (K.skel n).face σ i
      = Fin.cast (by rw [DeltaCx.skel_card_eq K n (by omega)])
          (K.face (Fin.cast (by rw [DeltaCx.skel_card_eq K n h]) σ) i) :=
  skelFace_eq K n h σ i

/-- The inclusion of the `n`-skeleton into `K`. -/
def DeltaCx.skelHom (K : DeltaCx) (n : ℕ) : (K.skel n).Hom K where
  map := fun {_} σ => skelMap K n σ
  map_face := fun {_} σ i => skelMap_face_face K n σ i

@[simp]
theorem DeltaCx.skelHom_map (K : DeltaCx) (n : ℕ) {j : ℕ} (σ : Fin ((K.skel n).card j)) :
    (K.skelHom n).map σ = skelMap K n σ := rfl

/-- The full skeleton of a `Δ`-complex has as many simplices as `K` itself. -/
theorem DeltaCx.skel_self_card (K : DeltaCx) (j : ℕ) : (K.skel K.dim).card j = K.card j := by
  by_cases h : j ≤ K.dim
  · rw [DeltaCx.skel_card]; exact skelCard_eq K h
  · rw [DeltaCx.skel_card, skelCard_eq_zero K (by omega), K.card_eq_zero j (by omega)]

/-- Inclusion of the `n`-skeleton in the `m`-skeleton for `n ≤ m`, on simplices. -/
def skelHomOfLe (K : DeltaCx) {n m : ℕ} (h : n ≤ m) {j : ℕ}
    (σ : Fin (skelCard K n j)) : Fin (skelCard K m j) :=
  if hk : j ≤ n then
    Fin.cast (by rw [skelCard_eq K hk, skelCard_eq K (by omega)]) σ
  else
    Fin.elim0 (Fin.cast (by rw [skelCard_eq_zero K (by omega)]) σ)

end

end Work.DeltaHomology
