import Mathlib
import Submission.Work.GCBasics.Points

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GCBasics

open CategoryTheory AlgebraicGeometry in
/-- A field-valued point of a glued scheme `D.glued` lands in one of the pieces: there is an
index `i` and a point `q : Spec F ⟶ D.U i` whose composite with the open immersion `D.ι i`
is `p`.

This is the point-level statement underlying `FPt.factor_of_landsIn`: the pieces `D.U i`
cover `D.glued`, and since `Spec F` has a single point, the whole image of `p` lies in the
open subprescheme `Set.range (D.ι i)`, so `p` lifts along the open immersion `D.ι i`. -/
theorem fpt_exists_factor (D : AlgebraicGeometry.Scheme.GlueData) {F : Type _} [Field F]
    (p : AlgebraicGeometry.Spec (CommRingCat.of F) ⟶ D.glued) :
    ∃ (i : D.J) (q : AlgebraicGeometry.Spec (CommRingCat.of F) ⟶ D.U i),
      q ≫ D.ι i = p := by
  obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective (p (IsLocalRing.closedPoint F))
  have hle : Set.range p ⊆ Set.range (D.ι i) := by
    rintro _ ⟨s, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint s).map p.continuous).mem_open
      (IsOpenImmersion.isOpen_range (D.ι i)) ⟨y, hy⟩
  exact ⟨i, IsOpenImmersion.lift (D.ι i) p hle, IsOpenImmersion.lift_fac (D.ι i) p hle⟩

end Work.GCBasics
