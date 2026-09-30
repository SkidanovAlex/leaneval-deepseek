import Mathlib
import Submission.Work.GCBasics.Points

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GCBasics

open CategoryTheory in
/-- Two morphisms of `K`-schemes out of a reduced `K`-scheme which agree on the canonical
`κ(x)`-point of `X` at every point `x` are equal, provided the target is separated over `K`.

This is Mathlib's `AlgebraicGeometry.ext_of_fromSpecResidueField_eq` with `S = univ`,
transported along the identification `(resPt X x).left = X.fromSpecResidueField x`: the
closed subscheme of `X` on which `f` and `g` agree is closed (separatedness of `Y` over
`K`) and contains every point of `X`, hence is all of `X` because `X` is reduced. -/
theorem hom_ext_of_resPt {K : Type _} [Field K] {X Y : Work.GCBasics.Sch K}
    [AlgebraicGeometry.IsReduced X.left] [AlgebraicGeometry.IsSeparated Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : X.left, Work.GCBasics.resPt (K := K) X x ≫ f =
      Work.GCBasics.resPt (K := K) X x ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  refine AlgebraicGeometry.ext_of_fromSpecResidueField_eq f.left g.left Y.hom Set.univ
    dense_univ ?_ ?_
  · rintro x -
    have hx := congrArg Over.Hom.left (h x)
    simpa [Work.GCBasics.resPt_left, Over.comp_left] using hx
  · rw [Over.w f, Over.w g]

end Work.GCBasics
