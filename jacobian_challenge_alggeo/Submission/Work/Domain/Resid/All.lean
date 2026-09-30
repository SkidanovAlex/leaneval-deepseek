/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RESID (area DM): the residue map exists

This is the assembly of the RESID layer of area DM: the residue map of `ResidData` satisfies
the specification `ResidMap` (VALUE and DEFINED), hence exists.

* `Work.Domain.Resid.ResidData.residMap_spec` — the specification;
* `Work.Domain.Resid.exists_residMap` — the existence, in the form of the interface
  `Work.GroupChunk.Resid` of area `GC` (see `Resid/GCAdapter.lean` for the conversion).
-/
import Submission.Work.Domain.Resid.residMap_value
import Submission.Work.Domain.Resid.residMap_mem_domain
import Submission.Work.Domain.Resid.canonPt_generic
import Submission.Work.Domain.Resid.canonPt_closed
import Submission.Work.Domain.Resid.fromSpecStalk_algebraMap
import Submission.Work.Domain.Resid.exists_algHom_fractionRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.Domain.Resid

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} [SpecLin.DivBase C]
  {symGeom : ∀ n, SpecLin.SymGeom C n} {g : ℕ}

/-- **RESID.**  The residue map attached to the data satisfies the RESID specification: it is
defined over `K`, its values represent the class of `divD symGeom a b p`, and it is defined at
every point where that class has `ℓ = 1`. -/
theorem ResidData.residMap_spec (D : ResidData (K := K) symGeom g) {X : Sch K}
    [IsIntegral X.left] [IsLocallyNoetherian X.left]
    (hX : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    {r m : ℕ} (hred : IsReduced X.left) (hsep : IsSeparated ((symGeom m).S).hom)
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S) (hm : g ≤ m) :
    ResidMap symGeom hred hsep a b (D.residMap a b hm) :=
  ⟨D.residMap_isOver a b hm,
    fun p hp => residMap_value D hX hred hsep a b hm p hp,
    fun x hx => residMap_mem_domain D hX a b hm x hx⟩

/-- **RESID exists.**  For morphisms `a : X ⟶ Sym^r C`, `b : X ⟶ Sym^{r+m} C` with `m ≥ g`,
there is a rational map `X ⤏ Sym^m C` whose values are the effective representatives of the
class of `divOf (b p) - divOf (a p)` and which is defined at every point where that class has
`ℓ = 1`. -/
theorem exists_residMap (D : ResidData (K := K) symGeom g) {X : Sch K}
    [IsIntegral X.left] [IsLocallyNoetherian X.left]
    (hX : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    {r m : ℕ} (hred : IsReduced X.left) (hsep : IsSeparated ((symGeom m).S).hom)
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S) (hm : g ≤ m) :
    ∃ σ : X.left ⤏ (symGeom m).S.left, ResidMap symGeom hred hsep a b σ :=
  ⟨D.residMap a b hm, D.residMap_spec hX hred hsep a b hm⟩

end Work.Domain.Resid
