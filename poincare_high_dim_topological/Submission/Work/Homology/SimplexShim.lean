import Submission.Work.Homology.SimplexShimHomeo

/-!
# Shim between the v4.33 and v4.34 models of the standard simplex

In Lean v4.34 the topological `n`-simplex is the structure `Convexity.StdSimplex ℝ (Fin (n+1))`
(finitely supported probability distributions), while the "old" (now deprecated) model is the
set `stdSimplex ℝ (Fin (n+1))` of functions `Fin (n+1) → ℝ` that are nonnegative and sum to one.
Older formalisations (e.g. the fleet's `Work.Cohomology` subdivision chapter) are written against
the old model, so we export

* `Work.Homology.stdHomeo`, the canonical homeomorphism between the two;
* `Work.Homology.toSSetObjEquiv'`, a v4.33-shaped replacement for `TopCat.toSSetObjEquiv` landing in
  continuous maps *out of the old simplex*;
* the naturality lemmas `toSSetObjEquiv'_δ_apply`, `toSSetObjEquiv'_naturality_apply` and
  `toSSetObjEquiv'_map_apply`, which are what the ported proofs rewrite with.
-/

set_option linter.deprecated false

open CategoryTheory AlgebraicTopology
open scoped Simplicial

namespace Work.Homology

noncomputable section

/-- The canonical homeomorphism from the v4.34 structure-based standard simplex to the
(deprecated) v4.33 set-based one, sending `w` to the function `i ↦ w.weights i`. -/
def stdHomeo : ∀ n : ℕ, Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ _root_.stdSimplex ℝ (Fin (n + 1)) :=
  Classical.choose SimplexShimHomeo

theorem stdHomeo_apply (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    ((stdHomeo n w : _root_.stdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) → ℝ) i = w.weights i :=
  (Classical.choose_spec SimplexShimHomeo).1 n w i

theorem stdHomeo_map (m n : ℕ) (f : Fin (m + 1) → Fin (n + 1))
    (w : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    stdHomeo n (Convexity.StdSimplex.map f w) = _root_.stdSimplex.map f (stdHomeo m w) :=
  (Classical.choose_spec SimplexShimHomeo).2 m n f w

/-- The inverse-compatibility of `stdHomeo` with the simplex maps. -/
theorem stdHomeo_symm_map (m N : ℕ) (f : Fin (m + 1) → Fin (N + 1))
    (z : _root_.stdSimplex ℝ (Fin (m + 1))) :
    Convexity.StdSimplex.map f ((stdHomeo m).symm z) =
      (stdHomeo N).symm (_root_.stdSimplex.map f z) := by
  apply (stdHomeo N).injective
  rw [stdHomeo_map, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

/-- A v4.33-shaped replacement for `TopCat.toSSetObjEquiv`: an `n`-simplex of the singular
simplicial set of `X` is a continuous map out of the *old* standard simplex. -/
def toSSetObjEquiv' (X : TopCat) (n : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj X).obj n ≃
      C(_root_.stdSimplex ℝ (Fin (n.unop.len + 1)), X) :=
  (X.toSSetObjEquiv n).trans
    (Homeomorph.continuousMapCongr (stdHomeo n.unop.len) (Homeomorph.refl X))

theorem toSSetObjEquiv'_apply (X : TopCat) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n)
    (z : _root_.stdSimplex ℝ (Fin (n.unop.len + 1))) :
    toSSetObjEquiv' X n x z = X.toSSetObjEquiv n x ((stdHomeo n.unop.len).symm z) := by
  simp [toSSetObjEquiv', Homeomorph.continuousMapCongr_apply]

/-- Naturality of `toSSetObjEquiv'` in the simplex category. -/
theorem toSSetObjEquiv'_naturality_apply {X : TopCat} {n m : SimplexCategory} (f : n ⟶ m)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op m))
    (z : _root_.stdSimplex ℝ (Fin (n.len + 1))) :
    toSSetObjEquiv' X (Opposite.op n) ((TopCat.toSSet.obj X).map f.op x) z =
      toSSetObjEquiv' X (Opposite.op m) x (_root_.stdSimplex.map f z) := by
  rw [toSSetObjEquiv'_apply, toSSetObjEquiv'_apply, TopCat.toSSetObjEquiv_naturality_apply]
  rw [stdHomeo_symm_map]

/-- The face formula for `toSSetObjEquiv'`. -/
theorem toSSetObjEquiv'_δ_apply {X : TopCat} {n : ℕ}
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) (z : _root_.stdSimplex ℝ (Fin (n + 1))) :
    toSSetObjEquiv' X (Opposite.op (SimplexCategory.mk n)) ((TopCat.toSSet.obj X).δ i x) z =
      toSSetObjEquiv' X (Opposite.op (SimplexCategory.mk (n + 1))) x
        (_root_.stdSimplex.map i.succAbove z) := by
  rw [toSSetObjEquiv'_apply, toSSetObjEquiv'_apply, TopCat.toSSetObjEquiv_δ_apply]
  rw [stdHomeo_symm_map]

/-- Naturality of `toSSetObjEquiv'` in the space. -/
theorem toSSetObjEquiv'_map_apply {X Y : TopCat} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n) (z : _root_.stdSimplex ℝ (Fin (n.unop.len + 1))) :
    toSSetObjEquiv' Y n ((TopCat.toSSet.map f).app n x) z = f (toSSetObjEquiv' X n x z) := by
  rw [toSSetObjEquiv'_apply, toSSetObjEquiv'_apply]
  rfl

/-- The (deprecated) set-based standard 0-simplex is a subsingleton; this instance existed for
the old definition and is needed by the ported subdivision files. -/
instance instSubsingletonStdSimplexOne : Subsingleton (_root_.stdSimplex ℝ (Fin 1)) where
  allEq a b := by
    apply Subtype.ext
    funext i
    have ha : (a : Fin 1 → ℝ) 0 = 1 := by simpa using a.2.2
    have hb : (b : Fin 1 → ℝ) 0 = 1 := by simpa using b.2.2
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact ha.trans hb.symm

/-- Variant of `instSubsingletonStdSimplexOne` with the index written as `0 + 1`; the ported
subdivision files produce the index in this shape. -/
instance instSubsingletonStdSimplexZeroSucc : Subsingleton (_root_.stdSimplex ℝ (Fin (0 + 1))) :=
  instSubsingletonStdSimplexOne

end

end Work.Homology
