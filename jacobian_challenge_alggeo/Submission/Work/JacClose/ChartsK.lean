/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacClose (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.C2)
-/
import Submission.Work.Charts.GalCharts_toCharts
import Submission.Work.BcDiv.All

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area JacClose, C2 — the Γ-keeping transport `GalCharts → Charts` over `k'`

`Work.Charts.GalCharts.toCharts` produces the covering `Charts C_{k'} R' P0'` of the base-changed
curve from the Galois-equivariant covering `GalCharts C R P0` over `k` and a comparison
`B : SymBC R k' R'` of symmetric powers — but only as a `Nonempty`, so that the chart `d'` and
the centres `B.pts.symm ∘ E` of the produced covering cannot be named.  Area `JacClose` needs
them *by name*: the `Γ`-orbit argument of §2.C6 has to compare the centres `E (act σ i)` of the
`k`-level covering with the centres of the `k'`-level one.

This file therefore re-issues the `toCharts` term as a **definition**
`Work.Charts.GalCharts.chartsK'`, with its two defining equations

* `Work.Charts.GalCharts.chartsK'_V` — `(chartsK' …).d.V = B.β ⁻¹ᵁ D.d.V`;
* `Work.Charts.GalCharts.chartsK'_E` — `(chartsK' …).E i = B.pts.symm (D.E i)`,

and the transport lemma for the chart relation at an *arbitrary* tower of field structures
(`IsScalarTower k k' F`, not just `F = k'`):

* `Work.Charts.GalCharts.inChart_of_inChart_k` (TL′): if the class `B.pic0Map c` of a class `c`
  over `F ⊇ k' ⊇ k` lies in the `k`-level chart of the centre `E i`, then `c` lies in the
  `k'`-level chart of the transported centre `B.pts.symm (E i)`.

TL′ is the `cov` step of `toCharts` with `σ = 1` replaced by an arbitrary tower structure; it is
what makes the `Γ`-orbit argument of §2.C6 work, where the structure `k → k' → F` on the residue
field `F` is *twisted* by `σ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K] {C : Curve K} [Work.SpecLin.DivBase C]

/-! ### The Γ-keeping transport -/

variable {R : RochData C} [Work.SpecLin.SymGeom C R.g]
variable {P0 : unitSch K ⟶ C.toOver}

namespace GalCharts

/-- **C2: `toCharts` as a definition.**  The covering of `Pic⁰(C_{k'})` over `k'` obtained from
the Galois-equivariant covering `D` over `k` and the comparison `B` of symmetric powers: the
base-changed Brill–Noether chart is `B.β ⁻¹ᵁ D.d.V` and the centres are the `B.pts`-preimages of
the centres of `D`. -/
noncomputable def chartsK' (D : GalCharts C R P0) (db : Work.SpecLin.DivBase (C.baseChange D.k'))
    (R' : RochData (C.baseChange D.k')) (sg : Work.SpecLin.SymGeom (C.baseChange D.k') R'.g)
    (P0' : unitSch D.k' ⟶ (C.baseChange D.k').toOver)
    (B : @SymBC K _ C _ R _ D.k' _ _ db R' sg) :
    @Charts D.k' _ (C.baseChange D.k') db R' sg P0' := by
  letI : Work.SpecLin.DivBase (C.baseChange D.k') := db
  letI : Work.SpecLin.SymGeom (C.baseChange D.k') R'.g := sg
  haveI hβ : IsAffineHom B.β := B.isAffineHom_β
  let chart : (Sym (C.baseChange D.k') R'.g).left.Opens := B.β ⁻¹ᵁ D.d.V
  have hchart : IsAffineOpen chart := IsAffineOpen.preimage D.d.isAffineOpen_V B.β
  have hii : ∀ {F : Type u} [Field F] [Algebra D.k' F]
      (p : FPt (Sym (C.baseChange D.k') R'.g) F),
      RPt.LandsIn p ((Sym (C.baseChange D.k') R'.g).left.basicOpen
        (1 : Γ((Sym (C.baseChange D.k') R'.g).left, chart))) →
      iOf (C.baseChange D.k') R'.W (divOf p) = 0 := by
    intro F _ _ p hp
    letI : Algebra K F := compAlgebra K D.k' F
    haveI hST : IsScalarTower K D.k' F := isScalarTower_compAlgebra K D.k' F
    rw [Scheme.basicOpen_one] at hp
    have hp' : (B.pts p).LandsIn D.d.V := (B.landsIn_preimage D.d p).mp hp
    have h1 : ell (C.baseChange D.k') (divOf p) = 1 := by
      rw [B.ell_eq (divOf p), B.pts_divOf p]
      exact D.d.ell_eq_one_of_landsIn (B.pts p) hp'
    exact (R'.i_eq_zero_iff_ell_eq_one (Ddeg_divOf p)).mpr h1
  have hne : (Sym (C.baseChange D.k') R'.g).left.basicOpen
      (1 : Γ((Sym (C.baseChange D.k') R'.g).left, chart)) ≠ ⊥ := by
    rw [Scheme.basicOpen_one]
    change B.β ⁻¹ᵁ D.d.V ≠ ⊥
    intro hbot
    apply D.d.ne_bot
    rw [← le_bot_iff]
    intro x hx
    obtain ⟨y, hy⟩ := B.surjective_β x
    have hy' : y ∈ (B.β ⁻¹ᵁ D.d.V :
        (Sym (C.baseChange D.k') R'.g).left.Opens) := by
      rw [Scheme.Hom.mem_preimage, hy]
      exact hx
    rw [hbot] at hy'
    exact (TopologicalSpace.Opens.mem_bot.mp hy').elim
  let d' : BNData (C.baseChange D.k') R' :=
    BNData.mk B.Q' B.U' B.hU' B.h' B.h_mem' B.h_span' chart hchart
      (1 : Γ((Sym (C.baseChange D.k') R'.g).left, chart)) hii hne
  refine Charts.mk d' D.ι (fintype := D.fintype)
    (fun i => (B.pts (F := D.k')).symm (D.E i)) ?_
  intro F _ _ c
  letI : Algebra K F := compAlgebra K D.k' F
  haveI hST : IsScalarTower K D.k' F := isScalarTower_compAlgebra K D.k' F
  obtain ⟨i, hi⟩ := D.orbit_cov (IsScalarTower.toAlgHom K D.k' F) (B.pic0Map c)
  have hi1 : InChart D.d (RPt.map (IsScalarTower.toAlgHom K D.k' F) (D.E i))
      (B.pic0Map c) := by simpa using hi 1
  obtain ⟨y, hy, hyc⟩ := hi1
  refine ⟨i, (B.pts (F := F)).symm y, ?_, ?_⟩
  · rw [BNData.V, Scheme.basicOpen_one, B.landsIn_preimage D.d, Equiv.apply_symm_apply]
    exact hy
  · apply B.pic0Map_injective
    rw [B.pic0Map_chartClass, Equiv.apply_symm_apply, B.pts_symm_map (D.E i)]
    exact hyc

/-- **C2, the chart of `chartsK'`.** -/
theorem chartsK'_V (D : GalCharts C R P0) (db : Work.SpecLin.DivBase (C.baseChange D.k'))
    (R' : RochData (C.baseChange D.k')) (sg : Work.SpecLin.SymGeom (C.baseChange D.k') R'.g)
    (P0' : unitSch D.k' ⟶ (C.baseChange D.k').toOver)
    (B : @SymBC K _ C _ R _ D.k' _ _ db R' sg) :
    (D.chartsK' db R' sg P0' B).d.V = B.β ⁻¹ᵁ D.d.V := by
  rw [chartsK', BNData.V, Scheme.basicOpen_one]

/-- **C2, the centres of `chartsK'`.** -/
theorem chartsK'_E (D : GalCharts C R P0) (db : Work.SpecLin.DivBase (C.baseChange D.k'))
    (R' : RochData (C.baseChange D.k')) (sg : Work.SpecLin.SymGeom (C.baseChange D.k') R'.g)
    (P0' : unitSch D.k' ⟶ (C.baseChange D.k').toOver)
    (B : @SymBC K _ C _ R _ D.k' _ _ db R' sg) (i : D.ι) :
    (D.chartsK' db R' sg P0' B).E i = (B.pts (F := D.k')).symm (D.E i) := rfl

/-- **TL′: the transport of the chart relation from the `k`-level to the `k'`-level**, for an
*arbitrary* tower of field structures `k → k' → F`.  This is the `cov` step of
`GalCharts.toCharts` with `σ = 1` replaced by an arbitrary `k`-embedding of `k'` into `F`. -/
theorem inChart_of_inChart_k (D : GalCharts C R P0)
    (db : Work.SpecLin.DivBase (C.baseChange D.k'))
    (R' : RochData (C.baseChange D.k')) (sg : Work.SpecLin.SymGeom (C.baseChange D.k') R'.g)
    (P0' : unitSch D.k' ⟶ (C.baseChange D.k').toOver)
    (B : @SymBC K _ C _ R _ D.k' _ _ db R' sg)
    {F : Type u} [Field F] [Algebra K F] [Algebra D.k' F] [IsScalarTower K D.k' F]
    (i : D.ι) (c : Pic0 (C.baseChange D.k') F)
    (h : InChart D.d (RPt.map (IsScalarTower.toAlgHom K D.k' F) (D.E i)) (B.pic0Map c)) :
    InChart (D.chartsK' db R' sg P0' B).d
      (RPt.map (IsScalarTower.toAlgHom D.k' D.k' F) ((D.chartsK' db R' sg P0' B).E i)) c := by
  letI : Work.SpecLin.DivBase (C.baseChange D.k') := db
  letI : Work.SpecLin.SymGeom (C.baseChange D.k') R'.g := sg
  obtain ⟨y, hy, hyc⟩ := h
  refine ⟨(B.pts (F := F)).symm y, ?_, ?_⟩
  · rw [chartsK'_V, B.landsIn_preimage D.d, Equiv.apply_symm_apply]
    exact hy
  · apply B.pic0Map_injective
    rw [chartsK'_E, B.pic0Map_chartClass, Equiv.apply_symm_apply, B.pts_symm_map (D.E i)]
    exact hyc

end GalCharts

end

end Work.Charts
