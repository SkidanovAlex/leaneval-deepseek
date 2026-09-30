import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Skeleta of a `Δ`-complex: the truncation data

The `n`-skeleton of a finite `Δ`-complex `K` is the subcomplex of simplices of
dimension `≤ n`.  This file contains the underlying index/cardinality data

* `skelCard K n j = if j ≤ n then K.card j else 0` — the number of `j`-simplices
  of the `n`-skeleton,
* `skelFace K n` — its face maps,

together with the two easy structural lemmas `skelCard_eq` and
`skelCard_eq_zero`.  The remaining proof obligations (the semi-simplicial
identities for `skelFace`, and vanishing of `skelCard` above `dim`) are proved in
`Submission/Work/DeltaHomology/skelFace_face_face.lean` and
`Submission/Work/DeltaHomology/skelCard_eq_zero_of_lt.lean`; the truncation
`DeltaCx` itself is assembled in `Submission/Work/DeltaHomology/Skeleton.lean`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

/-- The number of `j`-simplices of the `n`-skeleton of `K`. -/
def skelCard (K : DeltaCx) (n j : ℕ) : ℕ := if j ≤ n then K.card j else 0

theorem skelCard_eq (K : DeltaCx) {n j : ℕ} (h : j ≤ n) : skelCard K n j = K.card j := by
  rw [skelCard, if_pos h]

theorem skelCard_eq_zero (K : DeltaCx) {n j : ℕ} (h : n < j) : skelCard K n j = 0 := by
  rw [skelCard, if_neg (Nat.not_le.mpr h)]

/-- The `i`-th face of a `(k+1)`-simplex of the `n`-skeleton of `K`. -/
def skelFace (K : DeltaCx) (n : ℕ) {k : ℕ} (σ : Fin (skelCard K n (k + 1)))
    (i : Fin (k + 2)) : Fin (skelCard K n k) :=
  if h : k + 1 ≤ n then
    Fin.cast (by rw [skelCard_eq K (by omega)])
      (K.face (Fin.cast (by rw [skelCard_eq K h]) σ) i)
  else
    Fin.elim0 (Fin.cast (by rw [skelCard_eq_zero K (by omega)]) σ)

/-- The defining equation of `skelFace` in the non-vacuous case `k + 1 ≤ n`. -/
theorem skelFace_eq (K : DeltaCx) (n : ℕ) {k : ℕ} (h : k + 1 ≤ n)
    (σ : Fin (skelCard K n (k + 1))) (i : Fin (k + 2)) :
    skelFace K n σ i
      = Fin.cast (by rw [skelCard_eq K (by omega)])
          (K.face (Fin.cast (by rw [skelCard_eq K h]) σ) i) := by
  rw [skelFace, dif_pos h]

/-- The defining equation of `skelFace` in the vacuous case `n ≤ k`. -/
theorem skelFace_eq_of_not (K : DeltaCx) (n : ℕ) {k : ℕ} (h : ¬ (k + 1 ≤ n))
    (σ : Fin (skelCard K n (k + 1))) (i : Fin (k + 2)) :
    skelFace K n σ i = Fin.elim0 (Fin.cast (by rw [skelCard_eq_zero K (by omega)]) σ) := by
  rw [skelFace, dif_neg h]

/-- The inclusion of the `n`-skeleton of `K` into `K`, on `k`-simplices. -/
def skelMap (K : DeltaCx) (n : ℕ) {k : ℕ} (σ : Fin (skelCard K n k)) : Fin (K.card k) :=
  if h : k ≤ n then
    Fin.cast (by rw [skelCard_eq K h]) σ
  else
    Fin.elim0 (Fin.cast (by rw [skelCard_eq_zero K (by omega)]) σ)

/-- The defining equation of `skelMap` in the case `k ≤ n`. -/
theorem skelMap_eq (K : DeltaCx) (n : ℕ) {k : ℕ} (h : k ≤ n) (σ : Fin (skelCard K n k)) :
    skelMap K n σ = Fin.cast (by rw [skelCard_eq K h]) σ := by
  rw [skelMap, dif_pos h]

/-- The defining equation of `skelMap` in the vacuous case `n < k`. -/
theorem skelMap_eq_of_not (K : DeltaCx) (n : ℕ) {k : ℕ} (h : ¬ k ≤ n)
    (σ : Fin (skelCard K n k)) :
    skelMap K n σ = Fin.elim0 (Fin.cast (by rw [skelCard_eq_zero K (by omega)]) σ) := by
  rw [skelMap, dif_neg h]

end

end Work.DeltaHomology
