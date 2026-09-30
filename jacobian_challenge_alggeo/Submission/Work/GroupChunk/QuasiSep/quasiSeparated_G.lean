/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — quasi-separatedness of the group chunk `G D`

`G D` is a `K`-scheme locally of finite type over the field `K`.  A scheme locally of finite
type over a field is locally Noetherian (the affine charts are spectra of finitely generated
`K`-algebras, which are Noetherian), and a locally Noetherian scheme is quasi-separated
(Stacks 01OY: the intersection of two affine opens is a subset of the Noetherian space
underlying either of them, hence quasi-compact).  Consequently the structure morphism
`G D ⟶ Spec K` is quasi-separated, which is exactly the statement proved here.

The hypothesis `QuasiCompact (GSch D).hom` is not needed for this: quasi-separatedness is
local and does not require the source to be quasi-compact.
-/
import Mathlib
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Gluing.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.QuasiSep

universe u
open CategoryTheory in
open AlgebraicGeometry in
open scoped AlgebraicGeometry in
theorem quasiSeparated_G {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0)
    [LocallyOfFiniteType (Work.GroupChunk.GSch D).hom]
    [QuasiCompact (Work.GroupChunk.GSch D).hom] :
    QuasiSeparated (Work.GroupChunk.GSch D).hom := by
  -- `G D` is locally of finite type over the field `K`, hence locally Noetherian.
  have : IsLocallyNoetherian (Work.GroupChunk.GSch D).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Work.GroupChunk.GSch D).hom
  -- A locally Noetherian scheme is quasi-separated, hence so is `G D ⟶ Spec K`.
  exact QuasiSeparated.of_quasiSeparatedSpace _

end Work.GroupChunk.QuasiSep
