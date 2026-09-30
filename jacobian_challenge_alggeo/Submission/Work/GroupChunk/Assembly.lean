/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the group chunk `G D` as a scheme over `K`

Assembles the geometric properties of `GSch D` proved in the sibling files
(`Finiteness`, `QuasiSep`, `Proper`, `GeomProps`, `Separated`) into *instances*, so that
downstream areas may write `IsProper (GSch D).hom`, `GeometricallyIntegral (GSch D).hom`,
`IsIntegral (GSch D).left`, … without further ceremony.
-/
import Submission.Work.GroupChunk.Finiteness.loft_G
import Submission.Work.GroupChunk.Finiteness.quasiCompact_G
import Submission.Work.GroupChunk.QuasiSep.quasiSeparated_G
import Submission.Work.GroupChunk.Proper.isProper_G
import Submission.Work.GroupChunk.Separated.isSeparated_G
import Submission.Work.GroupChunk.GeomProps.geometricallyIrreducible_G
import Submission.Work.GroupChunk.GeomProps.geometricallyReduced_G
import Submission.Work.GroupChunk.GeomProps.connectedSpace_G
import Submission.Work.GroupChunk.AJ0Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K}
  {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]

instance instLocallyOfFiniteType_G (D : Input C P0) :
    LocallyOfFiniteType (GSch D).hom :=
  Finiteness.loft_G D

instance instQuasiCompact_G (D : Input C P0) : QuasiCompact (GSch D).hom :=
  Finiteness.quasiCompact_G D

instance instQuasiSeparated_G (D : Input C P0) : QuasiSeparated (GSch D).hom :=
  QuasiSep.quasiSeparated_G D

instance instIsSeparated_G (D : Input C P0) : IsSeparated (GSch D).hom :=
  Separated.isSeparated_G D

instance instIsProper_G (D : Input C P0) : IsProper (GSch D).hom :=
  Proper.isProper_G D

instance instGeometricallyIrreducible_G (D : Input C P0) :
    GeometricallyIrreducible (GSch D).hom :=
  GeomProps.geometricallyIrreducible_G D

instance instGeometricallyReduced_G (D : Input C P0) : GeometricallyReduced (GSch D).hom :=
  GeomProps.geometricallyReduced_G D

instance instGeometricallyIntegral_G (D : Input C P0) : GeometricallyIntegral (GSch D).hom := by
  rw [GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible]
  exact ⟨GeomProps.geometricallyReduced_G D, GeomProps.geometricallyIrreducible_G D⟩

instance instConnectedSpace_G (D : Input C P0) : ConnectedSpace (GSch D).left :=
  GeomProps.connectedSpace_G D

instance instIsIntegral_G (D : Input C P0) : IsIntegral (GSch D).left :=
  GeometricallyIntegral.isIntegral_of_subsingleton (GSch D).hom

instance instIsReduced_G (D : Input C P0) : IsReduced (GSch D).left :=
  inferInstance

instance instIsLocallyNoetherian_G (D : Input C P0) : IsLocallyNoetherian (GSch D).left :=
  LocallyOfFiniteType.isLocallyNoetherian (GSch D).hom

/-- `G D ⊗ G D` is reduced: it is the product of the geometrically reduced `G D` with itself
over the field `K`. -/
instance instIsReduced_tensor_G (D : Input C P0) : IsReduced ((GSch D) ⊗ (GSch D)).left := by
  show IsReduced (pullback (GSch D).hom (GSch D).hom)
  infer_instance

instance instIsLocallyNoetherian_tensor_G (D : Input C P0) :
    IsLocallyNoetherian ((GSch D ⊗ GSch D).left) := by
  show IsLocallyNoetherian (pullback (GSch D).hom (GSch D).hom)
  infer_instance

/-- `G D ⊗ G D ⊗ G D` is reduced. -/
instance instIsReduced_tensor3_G (D : Input C P0) :
    IsReduced (((GSch D) ⊗ (GSch D)) ⊗ (GSch D)).left := by
  show IsReduced (pullback (GSch D ⊗ GSch D).hom (GSch D).hom)
  infer_instance

end

end Work.GroupChunk
