/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area BcDiv, B7: the assembly of the `SymBC` bundle

For the concrete instances of area SY (`Work.SymQuot.instDivBase`,
`Work.SymQuot.instSymGeomOfNeZero`) and naming data supplied by the caller, this file assembles
the base-change comparison of symmetric powers in the shape of area CH's structure
`Work.Charts.SymBC`: the comparison `β : Sym^g(C_L) ⟶ Sym^g C` (affine, surjective), the induced
bijection `pts` on field points (natural in the field), the divisor identification `bcDiv`
(compatible with `divOf`, with linear equivalence, with `ℓ` and with the degree), together with
the naming data of the base-changed Brill–Noether chart.

The two `RochData` are only related by `hg : R'.g = R.g`; since the symmetric powers are indexed
by their exponent, all the statements of area BcDiv (which are proved at a single exponent) are
transported along the isomorphism `eqToIso (congrArg (·.Sym) hg)` of `Sym^{R'.g} C ≅ Sym^{R.g} C`.

## Main definitions

* `Work.BcDiv.ptsIsoEquiv` — the equivalence of point sets induced by an isomorphism of schemes;
* `Work.BcDiv.symBC` — the bundle `Work.Charts.SymBC R L R'` for the concrete instances.

## Main results

* `Work.BcDiv.symBCBundle` — the `Nonempty` form of the previous item.
-/
import Submission.Work.BcDiv.Basic
import Submission.Work.BcDiv.PbPt
import Submission.Work.BcDiv.Points
import Submission.Work.BcDiv.SymPts
import Submission.Work.BcDiv.Tower
import Submission.Work.BcDiv.Transport
import Submission.Work.BcDiv.deg_bcDiv
import Submission.Work.BcDiv.linEquiv_bcDiv_iff
import Submission.Work.BcDiv.ell_bcDiv
import Submission.Work.BcDiv.ramIdx_cmp
import Submission.Work.BcDiv.bcDiv_bc
import Submission.Work.BcDiv.bcDiv_ptDiv
import Submission.Work.BcDiv.betaK_surjective
import Submission.Work.BcDiv.betaK_isAffineHom
import Submission.Work.BcDiv.ptsK_map
import Submission.Work.BcDiv.powMap_betaK
import Submission.Work.BcDiv.divOf_ptsK
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.Charts.SymBC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.BcDiv

open Work.Charts

/-- **Post-composition with an isomorphism of `K`-schemes** induces an equivalence of the sets of
`F`-points. -/
noncomputable def ptsIsoEquiv {K : Type u} [Field K] {F : Type u} [Field F] [Algebra K F]
    {X Y : Work.SpecLin.Sch K} (e : X ≅ Y) :
    Work.SpecLin.FPt X F ≃ Work.SpecLin.FPt Y F where
  toFun p := p ≫ e.hom
  invFun q := q ≫ e.inv
  left_inv p := by simp
  right_inv q := by simp

@[simp]
theorem ptsIsoEquiv_toFun {K : Type u} [Field K] {F : Type u} [Field F] [Algebra K F]
    {X Y : Work.SpecLin.Sch K} (e : X ≅ Y) (p : Work.SpecLin.FPt X F) :
    ptsIsoEquiv e p = p ≫ e.hom := rfl

/-- **B7: the base-change comparison of symmetric powers in the shape of `Work.Charts.SymBC`**,
for the concrete instances of area SY and naming data supplied by the caller. -/
noncomputable def symBC {K : Type u} [Field K] {C : Curve K}
    (R : RochData C) {L : Type u} [Field L] [Algebra K L]
    (R' : RochData (C.baseChange L)) (hg : R'.g = R.g) [NeZero R.g] [NeZero R'.g]
    [SymQuot.CurveAffineCover C] [SymQuot.CurveAffineCover (C.baseChange L)]
    (Q' : (C.baseChange L).Place) (U' : (C.baseChange L).left.Opens)
    (hU' : IsAffineOpen U')
    (h' : Fin R'.g → ((C.baseChange L).baseChange L).functionField)
    (h_mem' : ∀ j,
      (0 : ((C.baseChange L).baseChange L).Div) ≤ ((C.baseChange L).baseChange L).div (h' j) + R'.W)
    (h_span' : ((C.baseChange L).baseChange L).L R'.W = Submodule.span L (Set.range h')) :
    SymBC R L R' := by
  let eS : SymQuot.Sym C R'.g ≅ SymQuot.Sym C R.g :=
    eqToIso (congrArg (fun k => SymQuot.Sym C k) hg)
  let bK : (SymQuot.Sym (C.baseChange L) R'.g).left ⟶ (SymQuot.Sym C R.g).left :=
    βK (K := K) (L := L) (C := C) R'.g ≫ eS.hom.left
  refine
    { β := bK
      isAffineHom_β := ?_
      surjective_β := ?_
      pts := fun {F} _ _ _ _ => (ptsK (K := K) (L := L) (F := F) R'.g).trans
        (ptsIsoEquiv (K := K) (F := F) eS)
      pts_left := ?_
      pts_map := ?_
      bcDiv := fun {F} _ _ _ _ => bcDiv
      pts_divOf := ?_
      linEquiv_iff := fun {F} _ _ _ _ D D' => linEquiv_bcDiv_iff D D'
      ell_eq := fun {F} _ _ _ _ D => ell_bcDiv D
      deg_eq := fun {F} _ _ _ _ D => deg_bcDiv D
      Q' := Q'
      U' := U'
      hU' := hU'
      h' := h'
      h_mem' := h_mem'
      h_span' := h_span' }
  · -- `β` is affine
    haveI : IsAffineHom (βK (K := K) (L := L) (C := C) R'.g) := betaK_isAffineHom R'.g
    exact inferInstance
  · -- `β` is surjective
    have h1 : Function.Surjective (βK (K := K) (L := L) (C := C) R'.g).base :=
      betaK_surjective R'.g
    have h2 : Function.Surjective (eS.hom.left).base :=
      (inferInstance : Surjective eS.hom.left).surj
    rw [Scheme.Hom.comp_base]
    exact h2.comp h1
  · -- `pts` is composition with `β`
    intro F _ _ _ _
      (p : Work.SpecLin.FPt (SymQuot.Sym (C.baseChange L) R'.g) F)
    dsimp only [bK]
    exact (congrArg (fun t => t ≫ Over.Hom.left eS.hom)
      (ptsK_left (K := K) (L := L) (F := F) R'.g p)).trans (Category.assoc _ _ _)
  · -- naturality of `pts`
    intro F F' _ _ _ _ _ _ _ _ e
      (p : Work.SpecLin.FPt (SymQuot.Sym (C.baseChange L) R'.g) F)
    exact ((congrArg (fun t => t ≫ eS.hom)
        (ptsK_map (K := K) (L := L) (F := F) (F' := F') e R'.g p)).trans
      (Category.assoc _ _ _))
  · -- `divOf` is compatible with `bcDiv`
    intro F _ _ _ _ p
    exact (divOf_ptsK (K := K) (L := L) (F := F) R'.g p).trans
      (divOf_eqToIso (C := C) hg (ptsK (K := K) (L := L) (F := F) R'.g p)).symm

/-- **B7, `Nonempty` form.** -/
theorem symBCBundle {K : Type u} [Field K] {C : Curve K}
    (R : RochData C) {L : Type u} [Field L] [Algebra K L]
    (R' : RochData (C.baseChange L)) (hg : R'.g = R.g) [NeZero R.g] [NeZero R'.g]
    [SymQuot.CurveAffineCover C] [SymQuot.CurveAffineCover (C.baseChange L)]
    (Q' : (C.baseChange L).Place) (U' : (C.baseChange L).left.Opens)
    (hU' : IsAffineOpen U')
    (h' : Fin R'.g → ((C.baseChange L).baseChange L).functionField)
    (h_mem' : ∀ j,
      (0 : ((C.baseChange L).baseChange L).Div) ≤ ((C.baseChange L).baseChange L).div (h' j) + R'.W)
    (h_span' : ((C.baseChange L).baseChange L).L R'.W = Submodule.span L (Set.range h')) :
    Nonempty (SymBC R L R') :=
  ⟨symBC R R' hg Q' U' hU' h' h_mem' h_span'⟩

end Work.BcDiv
