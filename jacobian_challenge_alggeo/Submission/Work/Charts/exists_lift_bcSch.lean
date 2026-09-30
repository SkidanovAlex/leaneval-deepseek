import Mathlib
import Submission.Work.GCBasics.Basic
import Submission.Work.Charts.FinBC

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Lifting a pair of points to the base change `X_L`

If `X` is a `K`-scheme, `L/K` a field extension and `F/K` a further field extension, then an
`F`-point `p` of `X` and an `F`-point `q` of `Spec L` (both over `K`) determine an `F`-point
of the base change `X_L = X ×_{Spec K} Spec L`: this is the universal property of the
pullback, and it is the only thing used here.  In the notation of
`Submission/Work/Charts/FinBC.lean` the resulting point `u` satisfies
`u ≫ bcFst X L = p` and `u ≫ bcSnd X L = q`.

Note that no compatibility hypothesis relating `p` and `q` is needed: both are morphisms of
`K`-schemes, so that the two composites `Spec F ⟶ Spec K` they induce agree automatically.
-/

set_option autoImplicit false

namespace Work.Charts

universe u

open CategoryTheory in
/-- **Existence of a point of the base change with prescribed projections.** -/
theorem exists_lift_bcSch {K : Type u} [Field K] (X : Work.GCBasics.Sch K)
    (L : Type u) [Field L] [Algebra K L]
    (F : Type u) [Field F] [Algebra K F]
    (p : Work.GCBasics.FPt X F) (q : Work.GCBasics.FPt (Work.GCBasics.specOf K L) F) :
    ∃ u : Work.GCBasics.FPt (Work.Charts.bcSch X L) F,
      u ≫ Work.Charts.bcFst X L = p ∧ u ≫ Work.Charts.bcSnd X L = q := by
  refine ⟨Over.homMk (Limits.pullback.lift p.left q.left ?_) ?_, ?_, ?_⟩
  · -- the two composites `Spec F ⟶ Spec K` induced by `p` and `q` agree
    simpa [Work.GCBasics.specOf, Over.mk_hom] using (Over.w p).trans (Over.w q).symm
  · -- the lift is a morphism of `K`-schemes
    simpa [Work.GCBasics.specOf, Over.mk_hom, Limits.pullback.lift_snd_assoc] using (Over.w q)
  · -- first projection
    apply Over.OverMorphism.ext
    show Limits.pullback.lift p.left q.left _ ≫
      Limits.pullback.fst X.hom (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K L)))
        = p.left
    rw [Limits.pullback.lift_fst]
  · -- second projection
    apply Over.OverMorphism.ext
    show Limits.pullback.lift p.left q.left _ ≫
      Limits.pullback.snd X.hom (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K L)))
        = q.left
    rw [Limits.pullback.lift_snd]

end Work.Charts
