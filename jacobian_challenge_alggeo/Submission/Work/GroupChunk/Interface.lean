/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC (`Submission/Work/GroupChunk`) — the interface

This file fixes the vocabulary of area **GC** of the Jacobian drive
(`NOTES_LEAD_jacobian_GC.md` §3.6): the group chunk `G D` attached to a chart datum
`D : Input C P0`, its group law and its Abel–Jacobi map.

Everything is over a field `K`, for a curve `C : CurveBasics.Curve K` and a base point
`P0 : 𝟙_ (Sch K) ⟶ C.toOver`.  The chart datum bundles the *outputs of the other areas*
of the drive as named hypotheses (see `NOTES.md` of this directory for the item-by-item
correspondence):

* `DivBase C` (area CB, `Work.SpecLin.DivBase`) — base change of divisors along field
  extensions;
* `symGeom : ∀ n, SymGeom C n` (area SY, `Work.SpecLin.SymGeom`) — the symmetric powers
  `Sym^n C`, their points `divOf`, and the splitting of effective divisors over algebraically
  closed fields;
* `addMap` — the addition of symmetric powers `Sym^m C ⊗ Sym^n C ⟶ Sym^{m+n} C` (SY);
* `constMap` — the constant map at an effective `K`-divisor (SY's `Sym.ofDiv`);
* `curveIso`, `curveAdd` — the identification `Sym^1 C = C` and the map
  `x ↦ x + (g-1)P0` used by the Abel–Jacobi map (SY);
* `geomIntegral_Sym` and friends — geometry of symmetric powers (SY);
* `ell_zero`, `rr7` — Riemann–Roch over an arbitrary field `F/K`: `ℓ(0) = 1`, and a divisor
  of degree at least the genus has an effective representative of the same degree (area RR);
* `V`, `ell_eq_one_of_landsIn`, `E`, `cov` (area CH) — the Brill–Noether chart `V`
  (an open with `ℓ = 1` everywhere on it) and the covering property COV;
* `resid_exists` (area DM, RESID) — the rational map `x ↦ |divOf b(x) - divOf a(x)|`,
  with its VALUE and DEFINED properties;
* `specLin` (area PR) is *not* an interface field here: it is proved on disk
  (`Work.SpecLin.specLin`) and is used directly by the separatedness argument.

The main constructions of the area (`σ`, `U`, `t`, `glueData`, `G`, `chart`, `cls`,
`AJSym`, `mul`, `inv`, `one`, `AJ₀`, `desc`) live in `Submission/Work/GroupChunk/Basic.lean`
and the files below it; they are all functions of `D : Input C P0`.

**Warning (notation).**  In files importing this module, do *not* `open scoped MonObj`:
that scope re-declares `ι` as notation for the inverse of a group object, which would make
the field name `Input.Idx`/the notation `D.ι` unparseable.  The lead's `D.ι` is available as
`D.Idx` or, through the abbreviation below, as `D.ι`.
-/
import Submission.Work.GCBasics.All
import Submission.Work.SpecLin.Interface
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Points.ptDiv_deg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K]

/-! ## Plumbing

The first definitions are pure bookkeeping: the unique morphism to the terminal object of
`Sch K`, and the value of a rational map at a point of its domain. -/

/-- A `K`-scheme which is separated over `Spec K` is a separated scheme.  This is the bridge
that lets the `Scheme`-level rational-map theory of Mathlib be used for `K`-schemes. -/
instance instSchemeIsSeparated (X : Sch K) [IsSeparated X.hom] : X.left.IsSeparated := by
  rw [Scheme.isSeparated_iff, ← terminal.comp_from X.hom]
  infer_instance

/-- The unique morphism from a `K`-scheme to the terminal object `𝟙_ (Sch K)`. -/
def toUnit (X : Sch K) : X ⟶ 𝟙_ (Sch K) :=
  SemiCartesianMonoidalCategory.toUnit X

theorem toUnit_unique {X : Sch K} (f g : X ⟶ 𝟙_ (Sch K)) : f = g :=
  SemiCartesianMonoidalCategory.toUnit_unique f g

theorem comp_toUnit {X Y : Sch K} (f : X ⟶ Y) : f ≫ toUnit Y = toUnit X :=
  SemiCartesianMonoidalCategory.comp_toUnit f

/-- Base change of a divisor from `K` to a field `F` over `K` (area CB). -/
def bcKF {C : CurveBasics.Curve K} [SpecLin.DivBase C] (F : Type u) [Field F] [Algebra K F]
    (E : Dv C K) : Dv C F :=
  SpecLin.DivBase.bc (Algebra.ofId K F) E

/-- The degree of the difference of the divisors of two points of `Sym^n C` is zero.  This is
the elementary computation that makes `picOf` below well defined. -/
theorem ddeg_sub_divOf {C : CurveBasics.Curve K} [SpecLin.DivBase C]
    (symGeom : ∀ n, SpecLin.SymGeom C n) (g : ℕ) {F : Type u} [Field F] [Algebra K F]
    (y z : FPt (symGeom g).S F) :
    Ddeg C F ((symGeom g).divOf y - (symGeom g).divOf z) = 0 := by
  rw [map_sub]
  rw [show Ddeg C F ((symGeom g).divOf y) = ((g : ℕ) : ℤ) from (symGeom g).divOf_deg y,
    show Ddeg C F ((symGeom g).divOf z) = ((g : ℕ) : ℤ) from (symGeom g).divOf_deg z,
    sub_self]

/-- **The value of a rational map at a point of its domain.**  If `p : Spec F ⟶ X` is a point
of a `K`-scheme `X` whose closed point lands in the domain of `σ : X ⤏ Y`, then `p` factors
through `σ.domain` (area GB, `RPt.factor_of_closed_landsIn`) and the composite with the
partial map `σ.toPartialMap` is a point of `Y`. -/
def value {X Y : Sch K} (hred : IsReduced X.left) (hsep : IsSeparated Y.hom)
    (σ : X.left ⤏ Y.left) (hσ : σ.IsOver (Spec (CommRingCat.of K)))
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F) (hp : RPt.LandsIn p σ.domain) :
    FPt Y F := by
  haveI : IsReduced X.left := hred
  haveI : IsSeparated Y.hom := hsep
  haveI : Y.left.IsSeparated := inferInstance
  have hdom : σ.toPartialMap.domain = σ.domain := rfl
  have hp' : RPt.LandsIn p σ.toPartialMap.domain := hdom.symm ▸ hp
  let q : RPt (Opens.toOver σ.toPartialMap.domain) F :=
    Classical.choose (RPt.factor_of_closed_landsIn (K := K) σ.toPartialMap.domain p hp')
  have hq : q ≫ Opens.ιOver σ.toPartialMap.domain = p :=
    (Classical.choose_spec
      (RPt.factor_of_closed_landsIn (K := K) σ.toPartialMap.domain p hp')).1
  have h1 : (σ.toPartialMap).toRationalMap.IsOver (Spec (CommRingCat.of K)) := by
    rw [Scheme.RationalMap.toRationalMap_toPartialMap]
    exact hσ
  have h2 : (σ.toPartialMap).IsOver (Spec (CommRingCat.of K)) :=
    (Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated
      (S := Spec (CommRingCat.of K))).mp h1
  have h3 : (σ.toPartialMap).hom ≫ Y.hom = (σ.toPartialMap).domain.ι ≫ X.hom := h2.1
  have hq' : q.left ≫ (σ.toPartialMap).domain.ι = p.left := by
    have h := congrArg Over.Hom.left hq
    simpa [Opens.ιOver_left] using h
  refine Over.homMk (q.left ≫ (σ.toPartialMap).hom) ?_
  rw [Category.assoc, h3, ← Category.assoc, hq']
  exact Over.Hom.w p

/-! ## The RESID interface (area DM) -/

/-- **RESID** (area DM, `NOTES_LEAD_jacobian_GC.md` §3.3): for morphisms
`a : X ⟶ Sym^r` and `b : X ⟶ Sym^{r+m}` with `m ≥ g`, a rational map
`σ : X ⤏ Sym^m` which computes the effective representative of the class
`[divOf b(x) - divOf a(x)]`, together with

* VALUE: at every field point of `X` in the domain of `σ`,
  `divOf σ(x) + divOf a(x) ~ divOf b(x)`;
* DEFINED: if `ℓ(divOf b(x) - divOf a(x)) = 1` at a point `x` of `X`, then `x` is in the
  domain of `σ`.

The hypotheses `hred`/`hsep` are the typeclass requirements of `RationalMap.toPartialMap`,
which is used in VALUE. -/
structure Resid (C : CurveBasics.Curve K) [SpecLin.DivBase C]
    (symGeom : ∀ n, SpecLin.SymGeom C n) {X : Sch K}
    (hred : IsReduced X.left) {r m : ℕ} (hsep : IsSeparated ((symGeom m).S).hom)
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S)
    (σ : X.left ⤏ (symGeom m).S.left) : Prop where
  /-- `σ` is a morphism over `K` (so that its values are `K`-points). -/
  isOver : σ.IsOver (Spec (CommRingCat.of K))
  /-- VALUE of RESID. -/
  value : ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt X F)
    (hp : RPt.LandsIn p σ.domain),
    LinEquiv C ((symGeom m).divOf (value hred hsep σ isOver p hp) + (symGeom r).divOf (p ≫ a))
      ((symGeom (r + m)).divOf (p ≫ b))
  /-- DEFINED of RESID. -/
  mem_domain : ∀ (x : X.left),
    ell C ((symGeom (r + m)).divOf (resPt X x ≫ b) - (symGeom r).divOf (resPt X x ≫ a)) = 1 →
    x ∈ σ.domain

/-! ## The chart datum -/

/-- **The chart datum of area GC**: the outputs of areas SY, RR, CH and DM (RESID) consumed by
the construction of the group chunk `G D`, together with the base point `P0`.

`D : Input C P0` carries the symmetric powers `D.Sym n = (D.symGeom n).S`, the chart
`D.V ⊆ Sym^g C` with `ℓ = 1` on it, the centres `D.E i` and the covering property `D.cov`
(area CH), and the RESID engine `D.resid_exists` (area DM). -/
class Input (C : CurveBasics.Curve K) (P0 : 𝟙_ (Sch K) ⟶ C.toOver) [SpecLin.DivBase C] where
  /-- the genus `g` of `C` (area RR: `g = genus C`). -/
  g : ℕ
  /-- the symmetric powers (area SY). -/
  symGeom : ∀ n, SpecLin.SymGeom C n
  /-- `Sym^n C` is proper over `K` (area SY). -/
  isProper_Sym : ∀ n, IsProper (symGeom n).S.hom
  /-- `Sym^n C` is geometrically integral over `K` (area SY). -/
  geomIntegral_Sym : ∀ n, GeometricallyIntegral (symGeom n).S.hom
  /-- `Sym^n C` is geometrically irreducible over `K` (area SY). -/
  geomIrred_Sym : ∀ n, GeometricallyIrreducible (symGeom n).S.hom
  /-- `Sym^n C` is locally of finite type over `K` (area SY). -/
  locallyOfFiniteType_Sym : ∀ n, LocallyOfFiniteType (symGeom n).S.hom
  /-- addition of symmetric powers (area SY). -/
  addMap : ∀ m n, (symGeom m).S ⊗ (symGeom n).S ⟶ (symGeom (m + n)).S
  /-- `divOf` of a sum of pullbacks is the sum of the divisors: the morphism-level form of
  the additivity of `divOf` (area SY). -/
  addMap_divOf : ∀ m n {X : Sch K} (u : X ⟶ (symGeom m).S) (v : X ⟶ (symGeom n).S)
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F),
    (symGeom (m + n)).divOf ((p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ addMap m n)
      = (symGeom m).divOf (p ≫ u) + (symGeom n).divOf (p ≫ v)
  /-- the constant map at an effective divisor of degree `n` (SY's `Sym.ofDiv`). -/
  constMap : ∀ (n : ℕ) (E : Dv C K), E.IsEffective → Ddeg C K E = n →
    (X : Sch K) → (X ⟶ (symGeom n).S)
  /-- `divOf` of a constant map is the base change of the divisor. -/
  constMap_divOf : ∀ (n : ℕ) (E : Dv C K) (hE : E.IsEffective) (hd : Ddeg C K E = n)
    (X : Sch K) {F : Type u} [Field F] [Algebra K F] (p : FPt X F),
    (symGeom n).divOf (p ≫ constMap n E hE hd X) = bcKF F E
  /-- the identification `Sym^1 C = C` (area SY). -/
  curveIso : C.toOver ⟶ (symGeom 1).S
  /-- `divOf` of a point of `C` (area SY). -/
  curveIso_divOf : ∀ {F : Type u} [Field F] [Algebra K F] (x : FPt C.toOver F),
    (symGeom 1).divOf (x ≫ curveIso) = SpecLin.ptDiv x
  /-- the divisor `[P0]` of the base point. -/
  P0Div : Dv C K
  /-- `[P0]` is effective. -/
  P0Div_isEffective : P0Div.IsEffective
  /-- the degree of `[P0]` is one. -/
  P0Div_deg : Ddeg C K P0Div = 1
  /-- `P0Div` **is** the divisor of the base point `P0`: at every field `F` over `K`, the
  divisor of the `F`-point `P0` is the base change of `P0Div`.  (This is not implied by
  effectivity and degree alone: `P0Div` could a priori be the divisor of a different
  `K`-point of `C`.) -/
  P0Div_ptDiv : ∀ {F : Type u} [Field F] [Algebra K F],
    SpecLin.ptDiv (toUnit (specOf K F) ≫ P0) = bcKF F P0Div
  /-- the map `x ↦ x + (g-1)P0` (area SY). -/
  curveAdd : C.toOver ⟶ (symGeom g).S
  /-- `divOf` of `x + (g-1)P0`. -/
  curveAdd_divOf : ∀ {F : Type u} [Field F] [Algebra K F] (x : FPt C.toOver F),
    (symGeom g).divOf (x ≫ curveAdd)
      = SpecLin.ptDiv x + (g - 1) • bcKF F P0Div
  /-- `ℓ(0) = 1` (area RR). -/
  ell_zero : ∀ {F : Type u} [Field F] [Algebra K F], ell C (0 : Dv C F) = 1
  /-- **RR7** (area RR): a divisor of degree at least the genus has an effective
  representative of the same degree. -/
  rr7 : ∀ {F : Type u} [Field F] [Algebra K F] (A : Dv C F), (g : ℤ) ≤ Ddeg C F A →
    ∃ E : Dv C F, E.IsEffective ∧ Ddeg C F E = Ddeg C F A ∧ LinEquiv C A E
  /-- the Brill–Noether chart `V ⊆ Sym^g C` (area CH). -/
  V : (symGeom g).S.left.Opens
  /-- `ℓ = 1` on the chart (area CH). -/
  ell_eq_one_of_landsIn : ∀ {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver V) F), ell C ((symGeom g).divOf (p ≫ Opens.ιOver V)) = 1
  /-- the index type of the centres (area CH); the lead writes `D.ι`. -/
  Idx : Type u
  /-- the index type is finite (area CH). -/
  fintype : Fintype Idx
  /-- the centres of the charts (area CH). -/
  E : Idx → FPt (symGeom g).S K
  /-- COV: every degree-zero class is representable in some chart (area CH). -/
  cov : ∀ {F : Type u} [Field F] [Algebra K F] (c : Pic0 C F), ∃ i : Idx,
    ∃ y : FPt (symGeom g).S F, RPt.LandsIn y V ∧
      Pic0.mk ((symGeom g).divOf y - (symGeom g).divOf (RPt.map (Algebra.ofId K F) (E i)))
        (ddeg_sub_divOf symGeom g y _) = c
  /-- RESID (area DM).

  **Fixed (defect D1).**  The original statement quantified over *every* integral `X`, but the
  only RESID theorem on disk (`Work.Domain.Resid.ResidData.exists_residMap`) needs
  `[IsLocallyNoetherian X.left]` and the integral closedness of the stalks of `X`; as stated the
  field could not be instantiated, and area `GC` uses it only at `X = Sym^g C` and
  `X = Sym^g C ⊗ Sym^g C` (where both hold, the first by local finiteness of type over a field
  and the second by the fields `normal_Sym`/`normal_SymSym` below). -/
  resid_exists : ∀ {X : Sch K} [IsIntegral X.left] [IsLocallyNoetherian X.left]
    (hX : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x)) (r m : ℕ)
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S), g ≤ m →
    ∃ σ : X.left ⤏ (symGeom m).S.left,
      Resid C symGeom (inferInstance : IsReduced X.left)
        (by haveI := isProper_Sym m; exact inferInstance) a b σ
  /-- **Normality of `Sym^g C`** (area `NM`): the local rings of the chart is integrally closed.
  Needed to instantiate `resid_exists` at `X = Sym^g C`. -/
  normal_Sym : ∀ x : ((symGeom g).S).left,
    IsIntegrallyClosed (((symGeom g).S).left.presheaf.stalk x)
  /-- **Normality of `Sym^g C ⊗ Sym^g C`** (area `NM`): needed to instantiate `resid_exists` at
  `X = Sym^g C ⊗ Sym^g C` (`Work.GroupChunk.GroupLaw.MulDefs`). -/
  normal_SymSym : ∀ x : ((symGeom g).S ⊗ (symGeom g).S).left,
    IsIntegrallyClosed (((symGeom g).S ⊗ (symGeom g).S).left.presheaf.stalk x)

namespace Input

variable {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
  (D : Input C P0)

/-- The `n`-th symmetric power of `C`. -/
abbrev Sym (n : ℕ) : Sch K := (D.symGeom n).S

/-- The index type of the centres, under the name `D.ι` used in the lead's notes. -/
abbrev ι : Type u := D.Idx

/-- The divisor of a point of `Sym^n C`. -/
abbrev divOf (n : ℕ) {F : Type u} [Field F] [Algebra K F] (p : FPt (D.Sym n) F) :
    Dv C F := (D.symGeom n).divOf p

/-- The centre `E i` of the `i`-th chart, base changed to `F`. -/
abbrev EF (i : D.Idx) {F : Type u} [Field F] [Algebra K F] : FPt (D.Sym D.g) F :=
  RPt.map (Algebra.ofId K F) (D.E i)

/-- The divisor of the centre `E i` over `K`. -/
abbrev EDiv (i : D.Idx) : Dv C K := (D.symGeom D.g).divOf (D.E i)

theorem EDiv_isEffective (i : D.Idx) : (D.EDiv i).IsEffective :=
  (D.symGeom D.g).divOf_isEffective (D.E i)

theorem EDiv_deg (i : D.Idx) : Ddeg C K (D.EDiv i) = (D.g : ℤ) :=
  (D.symGeom D.g).divOf_deg (D.E i)

/-- The class of a point of `Sym^g C`, relative to the chart centre `E i`. -/
def picOf (i : D.Idx) {F : Type u} [Field F] [Algebra K F] (p : FPt (D.Sym D.g) F) :
    Pic0 C F :=
  Pic0.mk (D.divOf D.g p - D.divOf D.g (D.EF i)) (ddeg_sub_divOf D.symGeom D.g p (D.EF i))

theorem picOf_def (i : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (D.Sym D.g) F) :
    D.picOf i p = Pic0.mk (D.divOf D.g p - D.divOf D.g (D.EF i))
      (ddeg_sub_divOf D.symGeom D.g p (D.EF i)) := rfl

/-- `InChart i c`: the class `c` has a representative in the chart `V`, with base divisor
`E i` — i.e. there is a point `y` of `V` with `mk (divOf y - E i) = c`. -/
def InChart (i : D.Idx) {F : Type u} [Field F] [Algebra K F] (c : Pic0 C F) : Prop :=
  ∃ y : FPt (D.Sym D.g) F, RPt.LandsIn y D.V ∧ D.picOf i y = c

theorem cov' {F : Type u} [Field F] [Algebra K F] (c : Pic0 C F) :
    ∃ i : D.Idx, D.InChart i c := by
  obtain ⟨i, y, hy, hc⟩ := D.cov c
  exact ⟨i, y, hy, hc⟩

/-- The genus of `C`, as a natural number. -/
abbrev genus : ℕ := D.g

/-- `divOf` is compatible with base change of the field of definition (area SY). -/
theorem divOf_map (n : ℕ) {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (p : FPt (D.Sym n) F) :
    D.divOf n (RPt.map e p) = SpecLin.DivBase.bc e (D.divOf n p) :=
  (D.symGeom n).divOf_map e p

/-- The divisor of the base change of the centre `E i`. -/
theorem EF_divOf (i : D.Idx) {F : Type u} [Field F] [Algebra K F] :
    D.divOf D.g (D.EF i) = bcKF F (D.EDiv i) :=
  (D.symGeom D.g).divOf_map (Algebra.ofId K F) (D.E i)

end Input

/-! ## Geometry of the symmetric powers

The instances below turn the fields of `D : Input C P0` into typeclass instances, so that
downstream files may write `IsIntegral (D.Sym n).left`, `IsSeparated (D.Sym n).hom`,
`GeometricallyIntegral (D.Sym n).hom`, etc. without further ceremony. -/

namespace Input

variable {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]

instance instIsProper (D : Input C P0) (n : ℕ) : IsProper ((D.symGeom n).S).hom :=
  D.isProper_Sym n

instance instGeomIntegral (D : Input C P0) (n : ℕ) : GeometricallyIntegral ((D.symGeom n).S).hom :=
  D.geomIntegral_Sym n

instance instGeomIrred (D : Input C P0) (n : ℕ) : GeometricallyIrreducible ((D.symGeom n).S).hom :=
  D.geomIrred_Sym n

instance instLocallyOfFiniteType (D : Input C P0) (n : ℕ) :
    LocallyOfFiniteType ((D.symGeom n).S).hom :=
  D.locallyOfFiniteType_Sym n

instance instIsIntegral (D : Input C P0) (n : ℕ) : IsIntegral ((D.symGeom n).S).left :=
  GeometricallyIntegral.isIntegral_of_subsingleton ((D.symGeom n).S).hom

instance instIsReduced (D : Input C P0) (n : ℕ) : IsReduced ((D.symGeom n).S).left := by
  haveI : IsIntegral ((D.symGeom n).S).left := Input.instIsIntegral D n
  infer_instance

instance instIsSeparated (D : Input C P0) (n : ℕ) : IsSeparated ((D.symGeom n).S).hom := by
  haveI := D.isProper_Sym n
  infer_instance

end Input

end

end Work.GroupChunk
