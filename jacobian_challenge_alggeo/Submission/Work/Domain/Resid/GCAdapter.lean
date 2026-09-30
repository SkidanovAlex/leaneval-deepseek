/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RESID (area DM): the interface of area GC

Area `GC` (`Submission/Work/GroupChunk/Interface.lean`) declares the RESID interface
`Work.GroupChunk.Resid` (with the value `Work.GroupChunk.value`) and takes it, for a chart
datum, as a named input.  This file discharges that interface from area DM:

* `Work.Domain.Resid.ResidMap.toResid` — the specification of area DM implies the interface of
  area GC (`Work.Domain.Resid.valueOf` and `Work.GroupChunk.value` are definitionally equal);
* `Work.Domain.Resid.ResidData.ofInput` — the data of the residue map, read off a chart datum
  `D : Work.GroupChunk.Input C P0`, together with the invariance of `ℓ` under base change of
  the field (the field `pull_ell` of `Work.GCBasics.DivBaseChange`, an input of area `CB`);
* `Work.Domain.Resid.input_resid_exists` — **the field `resid_exists` of
  `Work.GroupChunk.Input`**, proved.

SPEC-LIN (area PR) and the invariance of `ℓ` under base change of the field (area CB) are taken
as named hypotheses, in the exact form in which they are declared in this area (the field
`specLin` of `Work.Domain.Resid.ResidData`, discharged by `Work.SpecLin.specLin`, and the field
`pull_ell` of `Work.GCBasics.DivBaseChange`).

**Note (contract).**  The two theorems are stated for an integral, locally Noetherian `X` whose
stalks are integrally closed: those are exactly the hypotheses of the DOM engine of area DM
(`Submission/Work/Domain/Main.lean`), which RESID consumes.  In the use made of RESID by area
GC (`X = Sym^g C`) they hold, the first by local finiteness of type and the second by area NM
(`Work.Normality.isIntegrallyClosed_stalk_sym`).
-/
import Submission.Work.Domain.Resid.All
import Submission.Work.GroupChunk.Interface

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

/-- The RESID specification of area DM is the RESID interface of area GC (`valueOf` and
`value` are definitionally equal). -/
theorem ResidMap.toResid {X : Sch K} {r m : ℕ} {hred : IsReduced X.left}
    {hsep : IsSeparated ((symGeom m).S).hom} {a : X ⟶ (symGeom r).S}
    {b : X ⟶ (symGeom (r + m)).S} {σ : X.left ⤏ (symGeom m).S.left}
    (h : ResidMap symGeom hred hsep a b σ) :
    Work.GroupChunk.Resid C symGeom hred hsep a b σ :=
  ⟨h.isOver, fun p hp => h.value p hp, h.mem_domain⟩

/-- The data of the residue map, read off a chart datum of area GC.  The invariance of `ℓ`
under base change of the field is the input of area `CB` recorded in
`Work.GCBasics.DivBaseChange`; SPEC-LIN is the theorem `Work.SpecLin.specLin` of area `PR`,
taken here as a named hypothesis. -/
def ResidData.ofInput {P0 : 𝟙_ (Sch K) ⟶ C.toOver} (D : Work.GroupChunk.Input C P0)
    (ell_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
      (e : F →ₐ[K] F') (A : Dv C F), ell C (SpecLin.DivBase.bc e A) = ell C A)
    (specLin : ∀ {n : ℕ} (G : SpecLin.SymGeom C n) (R : Type u) [CommRing R] [IsDomain R]
      [ValuationRing R] [Algebra K R] (a b : SpecLin.RPt G.S R),
      SpecLin.LinEquiv C (G.divOf (SpecLin.genPt R ≫ a)) (G.divOf (SpecLin.genPt R ≫ b)) →
      SpecLin.LinEquiv C (G.divOf (SpecLin.closedPt R ≫ a)) (G.divOf (SpecLin.closedPt R ≫ b))) :
    ResidData (K := K) D.symGeom D.g where
  addMap := D.addMap
  addMap_divOf := D.addMap_divOf
  rr7 := D.rr7
  isProper := D.isProper_Sym
  locallyOfFiniteType := D.locallyOfFiniteType_Sym
  ell_bc := ell_bc
  specLin := specLin

/-- **The field `resid_exists` of `Work.GroupChunk.Input`.**  Together with the invariance of
`ℓ` under base change of the field, the residue map exists for every pair `a`, `b` with
`m ≥ g`, on any integral, locally Noetherian `X` with integrally closed stalks (in particular
on `X = Sym^N C`). -/
theorem input_resid_exists {P0 : 𝟙_ (Sch K) ⟶ C.toOver} (D : Work.GroupChunk.Input C P0)
    (ell_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
      (e : F →ₐ[K] F') (A : Dv C F), ell C (SpecLin.DivBase.bc e A) = ell C A)
    (specLin : ∀ {n : ℕ} (G : SpecLin.SymGeom C n) (R : Type u) [CommRing R] [IsDomain R]
      [ValuationRing R] [Algebra K R] (a b : SpecLin.RPt G.S R),
      SpecLin.LinEquiv C (G.divOf (SpecLin.genPt R ≫ a)) (G.divOf (SpecLin.genPt R ≫ b)) →
      SpecLin.LinEquiv C (G.divOf (SpecLin.closedPt R ≫ a)) (G.divOf (SpecLin.closedPt R ≫ b))) :
    ∀ {X : Sch K} [IsIntegral X.left] [IsLocallyNoetherian X.left]
      (hX : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
      (r m : ℕ) (a : X ⟶ (D.symGeom r).S) (b : X ⟶ (D.symGeom (r + m)).S), D.g ≤ m →
      ∃ σ : X.left ⤏ (D.symGeom m).S.left,
        Work.GroupChunk.Resid C D.symGeom (inferInstance : IsReduced X.left)
          (by haveI := D.isProper_Sym m; exact inferInstance) a b σ := by
  intro X _ _ hX r m a b hm
  exact ⟨_, ResidMap.toResid
    ((ResidData.ofInput (K := K) D ell_bc specLin).residMap_spec hX inferInstance
      inferInstance a b hm)⟩

/-- **The field `resid_exists` of `Work.GroupChunk.Input`, for `X = Sym^n C`.**  This is the
form in which area GC uses RESID: on the symmetric powers themselves, where the local
Noetherianness follows from local finiteness of type (area SY) and the integral closedness of
the stalks is the input of area NM (`Work.Normality.isIntegrallyClosed_stalk_sym`, which needs
SY's affine chart cover of `Sym^n C`); that input is named here as `hstalk`, exactly as SPEC-LIN
and the invariance of `ℓ` are named. -/
theorem input_resid_exists_sym {P0 : 𝟙_ (Sch K) ⟶ C.toOver} (D : Work.GroupChunk.Input C P0)
    (ell_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
      (e : F →ₐ[K] F') (A : Dv C F), ell C (SpecLin.DivBase.bc e A) = ell C A)
    (specLin : ∀ {n : ℕ} (G : SpecLin.SymGeom C n) (R : Type u) [CommRing R] [IsDomain R]
      [ValuationRing R] [Algebra K R] (a b : SpecLin.RPt G.S R),
      SpecLin.LinEquiv C (G.divOf (SpecLin.genPt R ≫ a)) (G.divOf (SpecLin.genPt R ≫ b)) →
      SpecLin.LinEquiv C (G.divOf (SpecLin.closedPt R ≫ a)) (G.divOf (SpecLin.closedPt R ≫ b)))
    (n : ℕ)
    (hstalk : ∀ x : (D.Sym n).left,
      IsIntegrallyClosed ((D.Sym n).left.presheaf.stalk x))
    (r m : ℕ) (a : D.Sym n ⟶ (D.symGeom r).S) (b : D.Sym n ⟶ (D.symGeom (r + m)).S)
    (hm : D.g ≤ m) :
    ∃ σ : (D.Sym n).left ⤏ (D.symGeom m).S.left,
      Work.GroupChunk.Resid C D.symGeom (inferInstance : IsReduced (D.Sym n).left)
        (by haveI := D.isProper_Sym m; exact inferInstance) a b σ := by
  haveI : LocallyOfFiniteType (D.Sym n).hom := D.locallyOfFiniteType_Sym n
  haveI : IsLocallyNoetherian (D.Sym n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (D.Sym n).hom
  exact input_resid_exists (K := K) D ell_bc specLin hstalk r m a b hm

end Work.Domain.Resid
