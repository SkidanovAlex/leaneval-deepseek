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

/-- Two `Fin.cast`s along mutually inverse equations cancel.  This is the
bookkeeping lemma that absorbs the casts `skelFace` introduces when it is
unfolded in its non-vacuous case: after `skelFace` is rewritten by
`skelFace_eq`, the result is a `K.face` applied to a term of the form
`Fin.cast h' (Fin.cast h x)` with `h : a = b`, `h' : b = a`, which is `x` on the
nose. -/
private lemma finCast_comp_self {a b : ℕ} (h : a = b) (h' : b = a) (x : Fin a) :
    Fin.cast h' (Fin.cast h x) = x := by
  ext; simp

/-- The semi-simplicial identity for the face maps of the `n`-skeleton of a
`Δ`-complex, transported from `DeltaCx.face_face` through the casts defining
`skelFace`: `skelFace (skelFace σ (Fin.succ j)) i = skelFace (skelFace σ (Fin.castSucc i)) j`
for `i ≤ j`.  Cases: `k+2 ≤ n` (both sides are `K.face` up to self-casts, use
`DeltaCx.face_face` plus `Fin.ext`/`Fin.val_cast`/`Fin.cast_cast`/`Fin.cast_eq_self`),
`k+1 ≤ n < k+2` (then `σ : Fin (skelCard K n (k+2)) = Fin 0`, eliminate), and
`¬ k+1 ≤ n` (both sides are `Fin.elim0`, use `Subsingleton.elim`). Useful:
`skelFace_eq`, `skelFace_eq_of_not`. -/
theorem skelFace_face_face (K : DeltaCx) (n : ℕ) {k : ℕ} (σ : Fin (skelCard K n (k + 2)))
    (i j : Fin (k + 2)) (hij : i ≤ j) :
    skelFace K n (skelFace K n (k := k + 1) σ (Fin.succ j)) i
      = skelFace K n (skelFace K n (k := k + 1) σ (Fin.castSucc i)) j := by
  by_cases h2 : k + 2 ≤ n
  · -- Non-vacuous case: every `skelFace` involved is a `K.face` behind `Fin.cast`s.
    have h1 : k + 1 ≤ n := by omega
    rw [skelFace_eq K n h1, skelFace_eq K n (show k + 1 + 1 ≤ n by omega),
        skelFace_eq K n h1, skelFace_eq K n (show k + 1 + 1 ≤ n by omega)]
    apply Fin.ext
    simp only [Fin.val_cast]
    -- absorb the two casts surrounding the inner face `K.face (Fin.cast _ σ) _`
    simp only [finCast_comp_self]
    exact congrArg Fin.val (K.face_face (Fin.cast _ σ) i j hij)
  · by_cases h1 : k + 1 ≤ n
    · -- Middle case: `σ` lives in `Fin 0`.
      have hz : skelCard K n (k + 2) = 0 := skelCard_eq_zero K (by omega)
      exact Fin.elim0 (Fin.cast hz σ)
    · -- Vacuous case: the inner argument of the outer `skelFace` lives in `Fin 0`.
      have hz1 : skelCard K n (k + 1) = 0 := skelCard_eq_zero K (by omega)
      exact Fin.elim0 (Fin.cast hz1 (skelFace K n (k := k + 1) σ (Fin.succ j)))

end Work.DeltaHomology
