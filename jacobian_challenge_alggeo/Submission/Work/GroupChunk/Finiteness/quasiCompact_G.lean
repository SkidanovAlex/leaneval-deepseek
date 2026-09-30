import Mathlib
import Submission.Work.GroupChunk.AJSym
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Gluing.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.Finiteness

universe u

open CategoryTheory in
open AlgebraicGeometry in
open scoped AlgebraicGeometry in
/-- A morphism of schemes into a target whose underlying topological space is a subsingleton is
quasi-compact as soon as its source is quasi-compact as a topological space.  Indeed the only
subsets of the target are `∅` and `univ`. -/
lemma quasiCompact_of_subsingleton_target {X Y : Scheme} [Subsingleton Y] [CompactSpace X]
    (f : X ⟶ Y) : QuasiCompact f := by
  refine ⟨fun U _ _ => ?_⟩
  rcases Set.eq_empty_or_nonempty U with h | ⟨y, hy⟩
  · rw [h, Set.preimage_empty]; exact isCompact_empty
  · have hUuniv : U = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      rw [Subsingleton.elim z y]
      exact hy
    rw [hUuniv, Set.preimage_univ]
    exact isCompact_univ

open CategoryTheory in
open AlgebraicGeometry in
open scoped AlgebraicGeometry in
theorem quasiCompact_G {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0) :
    QuasiCompact (Work.GroupChunk.GSch D).hom := by
  -- `Sym^g C` is proper over the one-point scheme `Spec K`, hence compact.
  have hc : CompactSpace (D.Sym D.g).left := by
    haveI := D.isProper_Sym D.g
    exact QuasiCompact.compactSpace_of_compactSpace ((D.symGeom D.g).S).hom
  -- the Abel–Jacobi morphism `Sym^g C ⟶ G` is surjective, so `G` is compact too.
  haveI hG : CompactSpace (Work.GroupChunk.GSch D).left := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ.mpr (Work.GroupChunk.Input.AJSym_surjective D)]
    simpa only [Set.image_univ] using (isCompact_univ.image (D.AJSym).left.continuous)
  -- `Spec K` is a single point, so quasi-compactness is precisely compactness of the source.
  exact quasiCompact_of_subsingleton_target (Work.GroupChunk.GSch D).hom

end Work.GroupChunk.Finiteness
