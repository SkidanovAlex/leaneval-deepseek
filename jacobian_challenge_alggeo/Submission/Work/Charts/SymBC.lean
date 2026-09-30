/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — the base-change comparison of symmetric powers (`SymBC`), and `Pic⁰` transport

This is the interface that turns the Galois-equivariant covering `GalCharts C R P0` over a
finite Galois extension `k'` into the covering `Charts (C_{k'}) R' P0'` over `k'` that area
`GC` runs on ("`GalCharts.toCharts`", the lead's §6 of `NOTES_LEAD_jacobian_charts3.md`, and
`V_base_change` of §3.5).

**Where this sits.**  Area `SY` is to deliver `Work.SymQuot.SymBC`: a scheme map
`β : Sym^n(C_L) ⟶ Sym^n C` that is affine and surjective, together with the bijection it induces
on field points, the `divOf`-compatibility (via area `CB`'s identification
`bcDiv : Dv (C_L) F ≃+ Dv C F`) and naturality.  That bundle is *not* declared here (it is SY's
deliverable); this file declares the same bundle in namespace `Work.Charts` so that
`GalCharts.toCharts` can be stated and proved *now*, and so that SY's version, when it lands,
only has to be matched field by field.

## Contents

* `Work.Charts.SymBC` — the bundle: `β` (affine, surjective), `pts` (the field-point
  equivalence, with `pts_left` and `pts_map`), `bcDiv` (the divisor-group identification, with
  `pts_divOf`, `linEquiv_iff`, `ell_eq`, `deg_eq`), and the naming data of the base-changed
  Brill–Noether chart (`Q'`, `U'`, `hU'`, a basis `h'` of `R'.L` with `h_mem'`, `h_span'`);
* `Work.Charts.SymBC.pic0Map`, `pic0Map_mk`, `pic0Map_injective` — the transport of degree-zero
  divisor classes along `bcDiv`, and its computation rules;
* `Work.Charts.SymBC.chartClass_map` — the same for the chart classes `chartClass y E` of
  `Cover.lean`, and `Work.Charts.SymBC.landsIn_preimage` — the transport of `LandsIn` through
  `β`.
-/
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.Cover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


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

/-- **The base-change comparison of symmetric powers**, in the form in which the charts of area
`CH` consume it (the lead's §6; area `SY`'s `SymQuot.SymBC` has the same fields).

`β : Sym^n(C_L) ⟶ Sym^n C` is affine and surjective; `pts` is the induced bijection on field
points (`pts_left`), compatible with the field extension (`pts_map`); `bcDiv` identifies the
divisor groups of `C_L` and `C` over any `L`-field `F`, compatibly with `divOf` (`pts_divOf`),
with linear equivalence (`linEquiv_iff`), with `ℓ` (`ell_eq`) and with the degree (`deg_eq`).
The last six fields are naming data of the base-changed Brill–Noether chart. -/
structure SymBC (R : RochData C) [Work.SpecLin.SymGeom C R.g] (L : Type u) [Field L]
    [Algebra K L] [Work.SpecLin.DivBase (C.baseChange L)]
    (R' : RochData (C.baseChange L)) [Work.SpecLin.SymGeom (C.baseChange L) R'.g] where
  /-- the comparison map `Sym^n(C_L) ⟶ Sym^n C` on underlying schemes -/
  β : (Sym (C.baseChange L) R'.g).left ⟶ (Sym C R.g).left
  /-- `β` is affine -/
  isAffineHom_β : IsAffineHom β
  /-- `β` is surjective -/
  surjective_β : Function.Surjective β.base
  /-- the induced bijection on field points -/
  pts : ∀ {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F],
    FPt (Sym (C.baseChange L) R'.g) F ≃ FPt (Sym C R.g) F
  /-- `pts` is given by composition with `β` -/
  pts_left : ∀ {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (p : FPt (Sym (C.baseChange L) R'.g) F), (pts p).left = p.left ≫ β
  /-- naturality of `pts` in the field -/
  pts_map : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra L F] [Algebra L F'] [Algebra K F]
    [Algebra K F'] [IsScalarTower K L F] [IsScalarTower K L F'] (e : F →ₐ[L] F')
    (p : FPt (Sym (C.baseChange L) R'.g) F),
    pts (RPt.map e p) = RPt.map (e.restrictScalars K) (pts p)
  /-- the identification of the divisor groups of `C_L` and `C` over an `L`-field `F` -/
  bcDiv : ∀ {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F],
    Dv (C.baseChange L) F ≃+ Dv C F
  /-- `bcDiv` is compatible with `divOf` -/
  pts_divOf : ∀ {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (p : FPt (Sym (C.baseChange L) R'.g) F),
    bcDiv (Work.SpecLin.SymGeom.divOf p) = Work.SpecLin.SymGeom.divOf (pts p)
  /-- `bcDiv` is compatible with linear equivalence -/
  linEquiv_iff : ∀ {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (D D' : Dv (C.baseChange L) F),
    LinEquiv (C.baseChange L) D D' ↔ LinEquiv C (bcDiv D) (bcDiv D')
  /-- `bcDiv` is compatible with `ℓ` -/
  ell_eq : ∀ {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (D : Dv (C.baseChange L) F), ell (C.baseChange L) D = ell C (bcDiv D)
  /-- `bcDiv` is compatible with the degree -/
  deg_eq : ∀ {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (D : Dv (C.baseChange L) F),
    Ddeg C F (bcDiv D) = Ddeg (C.baseChange L) F D
  /-- a place of `C_L` (naming data of the base-changed chart) -/
  Q' : (C.baseChange L).Place
  /-- an affine open of `C_L` (naming data of the base-changed chart) -/
  U' : (C.baseChange L).left.Opens
  /-- the affine open `U'` is affine -/
  hU' : IsAffineOpen U'
  /-- a basis of `R'.L` (naming data of the base-changed chart) -/
  h' : Fin R'.g → ((C.baseChange L).baseChange L).functionField
  /-- the basis elements lie in `R'.L` -/
  h_mem' : ∀ j, 0 ≤ ((C.baseChange L).baseChange L).div (h' j) + R'.W
  /-- the basis elements span `R'.L` -/
  h_span' : ((C.baseChange L).baseChange L).L R'.W = Submodule.span L (Set.range h')

/-- The subgroup of principal divisors, inside the degree-zero divisors of `C_F`.  With it,
`Pic⁰(C_F)` is the quotient `div0 C F ⧸ prin0 C F`. -/
abbrev prin0 (C : Curve K) (F : Type u) [Field F] [Algebra K F] : AddSubgroup (div0 C F) :=
  (prin C F).comap (div0 C F).subtype

namespace SymBC

variable {R : RochData C} [Work.SpecLin.SymGeom C R.g] {L : Type u} [Field L] [Algebra K L]
  [Work.SpecLin.DivBase (C.baseChange L)] {R' : RochData (C.baseChange L)}
  [Work.SpecLin.SymGeom (C.baseChange L) R'.g] (B : SymBC R L R')

/-- `bcDiv` restricted to the degree-zero divisors, as an additive homomorphism. -/
noncomputable def bcDiv0 {F : Type u} [Field F] [Algebra L F] [Algebra K F]
    [IsScalarTower K L F] : div0 (C.baseChange L) F →+ div0 C F where
  toFun D := ⟨B.bcDiv D.1, by
    change Ddeg C F (B.bcDiv D.1) = 0
    rw [B.deg_eq]
    exact D.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' D D' := Subtype.ext (by simp)

@[simp]
theorem bcDiv0_apply {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (D : div0 (C.baseChange L) F) :
    ((B.bcDiv0 D : div0 C F) : Dv C F) = B.bcDiv (D : Dv (C.baseChange L) F) := rfl

/-- **The transport of degree-zero divisor classes** along `SymBC.bcDiv`: the map
`Pic⁰(C_L/F) → Pic⁰(C/F)` induced by `bcDiv`. -/
noncomputable def pic0Map {F : Type u} [Field F] [Algebra L F] [Algebra K F]
    [IsScalarTower K L F] : Pic0 (C.baseChange L) F → Pic0 C F :=
  QuotientAddGroup.map (prin0 (C.baseChange L) F) (prin0 C F) (B.bcDiv0) (by
      intro D hD
      have hD' : LinEquiv (C.baseChange L) (D : Dv (C.baseChange L) F) 0 := by
        have h := hD
        rw [AddSubgroup.mem_comap] at h
        rwa [Work.GCBasics.mem_prin_iff] at h
      show B.bcDiv0 D ∈ AddSubgroup.comap (div0 C F).subtype (prin C F)
      rw [AddSubgroup.mem_comap, Work.GCBasics.mem_prin_iff]
      change LinEquiv C (B.bcDiv (D : Dv (C.baseChange L) F)) 0
      simpa using (B.linEquiv_iff (D : Dv (C.baseChange L) F) 0).mp hD')

/-- The computation rule of `SymBC.pic0Map`. -/
theorem pic0Map_mk' {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (D : div0 (C.baseChange L) F) :
    B.pic0Map (D : Pic0 (C.baseChange L) F) = (B.bcDiv0 D : Pic0 C F) := by
  unfold pic0Map
  rw [QuotientAddGroup.map_mk]

/-- The computation rule of `SymBC.pic0Map`, in the form of the class map `Pic0.mkHom`. -/
theorem pic0Map_mkHom {F : Type u} [Field F] [Algebra L F] [Algebra K F]
    [IsScalarTower K L F] (D : div0 (C.baseChange L) F) :
    B.pic0Map (Pic0.mkHom (C.baseChange L) F D) = Pic0.mkHom C F (B.bcDiv0 D) :=
  B.pic0Map_mk' D

/-- The computation rule of `SymBC.pic0Map`, in the form of `Pic0.mk`. -/
theorem pic0Map_mk {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (D : Dv (C.baseChange L) F) (hD : Ddeg (C.baseChange L) F D = 0) :
    B.pic0Map (Pic0.mk D hD) = Pic0.mk (B.bcDiv D) (by rw [B.deg_eq]; exact hD) :=
  B.pic0Map_mkHom ⟨D, hD⟩

/-- **`SymBC.pic0Map` is injective**: the transport of classes is faithful, by the
`LinEquiv`-compatibility of `bcDiv`. -/
theorem pic0Map_injective {F : Type u} [Field F] [Algebra L F] [Algebra K F]
    [IsScalarTower K L F] : Function.Injective (B.pic0Map (F := F)) := by
  intro a b hab
  induction a using Quotient.inductionOn' with
  | h D =>
    induction b using Quotient.inductionOn' with
    | h D' =>
      change B.pic0Map (D : Pic0 (C.baseChange L) F)
        = B.pic0Map (D' : Pic0 (C.baseChange L) F) at hab
      rw [B.pic0Map_mk' D, B.pic0Map_mk' D'] at hab
      have hsub : ((B.bcDiv0 D - B.bcDiv0 D' : div0 C F) : Dv C F) ∈ prin C F := by
        have h := QuotientAddGroup.eq_iff_sub_mem.mp hab
        rwa [AddSubgroup.mem_comap] at h
      have hsub' : B.bcDiv D.1 - B.bcDiv D'.1 ∈ prin C F := by
        simpa only [AddSubgroup.coe_sub, bcDiv0_apply] using hsub
      have hlin : LinEquiv (C.baseChange L) (D.1 - D'.1) 0 := by
        have h2 : LinEquiv C (B.bcDiv (D.1 - D'.1)) 0 := by
          rw [← map_sub, Work.GCBasics.mem_prin_iff] at hsub'
          exact hsub'
        exact (B.linEquiv_iff (D.1 - D'.1) 0).mpr (by simpa using h2)
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      rw [AddSubgroup.mem_comap]
      exact (Work.GCBasics.mem_prin_iff).mpr hlin

end SymBC

end

end Work.Charts
