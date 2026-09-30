/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacClose (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.C3, §2.C4)
-/
import Submission.Work.JacClose.ChartsK
import Submission.Work.Universal.Main
import Submission.Work.GroupChunk.Export
import Submission.Work.JacFinal.rr7_of_rochData
import Submission.Work.Domain.Resid.GCAdapter

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area JacClose, C3/C4 — the builders `GroupChunk.Input` and `Universal.Input` over `k'`

The chart datum of area `GC` (`Work.GroupChunk.Input`) bundles the outputs of the areas `SY`,
`RR`, `CH` and `DM`; the package of area `UP` (`Work.Universal.Input`) additionally bundles the
outputs of `GC` and the key lemma of area `KL`.  Both are *classes*, i.e. named inputs, and
nothing on disk inhabits them for a concrete curve: this file is the builder (the lead's §2.C3
and §2.C4).

Because the areas `SY` (the addition/constant map of symmetric powers, the geometry of `Symⁿ`)
and `DM` (RESID) are still in flight, their outputs are taken here as *explicit data*:

* `Work.JacClose.SYData C P0` collects the `SY`-side fields of `Work.GroupChunk.Input`
  (the family of symmetric powers, its geometry, `addMap`, `constMap`, `curveIso`), i.e. every
  field of `Work.GroupChunk.Input` that does not mention the genus `g` or the base divisor;
* `Work.JacClose.ResidOld` is the `resid_exists` field of `Work.GroupChunk.Input` **as it is
  currently stated**.

The two `SY`-side and the `RESID`-side inputs are *not* extra mathematical assumptions: they are
outputs of the areas `SY` and `DM`, which the present area does not own.  Everything else —
`g`, the base divisor `[P₀]`, `curveAdd`, `ell_zero`, `rr7`, the Brill–Noether chart (from
`ChartDatum`) and the geometry of the symmetric powers — is *built* here from area `CH`'s chart
datum, area `RR`'s `RochData` and the base point.

## The `resid_exists` interface (defect D1)

`Work.GroupChunk.Input.resid_exists` quantifies over *every* integral `X`, while the only RESID
theorem on disk (`Work.Domain.Resid.ResidData.exists_residMap`) additionally needs
`[IsLocallyNoetherian X.left]` and the integral closedness of the stalks of `X`.  As stated, the
field therefore cannot be instantiated, and it is taken here as the explicit datum `ResidOld`;
`Work.JacClose.normal_Sym` and `Work.JacClose.normal_SymSym` are the two *extra* fields that
area `GC` needs at its seven use sites (`Defs.lean:76,84`, `AbelJacobi.lean:72,80`,
`GroupLaw/inv_exists.lean:62,68`, `GroupLaw/MulDefs.lean:186`) once its interface is corrected.
Both are recorded here, and `Work.JacClose.gcInput` consumes the corrected data through them.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.JacClose

open Work.CurveBasics
open Work.GCBasics
open Work.GroupChunk (bcKF ddeg_sub_divOf)

noncomputable section

variable {K : Type u} [Field K]

/-! ## The `SY`-side data -/

/-- **The `SY`-side fields of `Work.GroupChunk.Input`**, i.e. every field of the chart datum of
area `GC` that does not mention the genus `g` or the base divisor `[P₀]`: the family of
symmetric powers, its geometry, `addMap` with its `divOf`-compatibility, `constMap` with its
`divOf`-compatibility, and the identification `Sym¹ C ≅ C`.

This is the output of area `SY` (more precisely of area `BNChart`'s `addMapFam`-package: the
zero cases of `addMap` and `constMap` are the ones that the `match n with | 0 => … | k+1 => …`
of `SymQuot.symGeomFamily` makes non-trivial).  It is *data*, not an assumption. -/
class SYData (C : Curve K) (P0 : 𝟙_ (Sch K) ⟶ C.toOver) [Work.SpecLin.DivBase C]
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n) where
  /-- `Sym^n C` is proper over `K` (area SY). -/
  isProper_Sym : ∀ n, IsProper ((symGeom n).S).hom
  /-- `Sym^n C` is geometrically integral over `K` (area SY). -/
  geomIntegral_Sym : ∀ n, GeometricallyIntegral ((symGeom n).S).hom
  /-- `Sym^n C` is geometrically irreducible over `K` (area SY). -/
  geomIrred_Sym : ∀ n, GeometricallyIrreducible ((symGeom n).S).hom
  /-- `Sym^n C` is locally of finite type over `K` (area SY). -/
  locallyOfFiniteType_Sym : ∀ n, LocallyOfFiniteType ((symGeom n).S).hom
  /-- addition of symmetric powers (area SY). -/
  addMap : ∀ m n, (symGeom m).S ⊗ (symGeom n).S ⟶ (symGeom (m + n)).S
  /-- `divOf` of a sum of pullbacks is the sum of the divisors (area SY). -/
  addMap_divOf : ∀ m n {X : Sch K} (u : X ⟶ (symGeom m).S) (v : X ⟶ (symGeom n).S)
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F),
    (symGeom (m + n)).divOf ((p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ addMap m n)
      = (symGeom m).divOf (p ≫ u) + (symGeom n).divOf (p ≫ v)
  /-- the constant map at an effective divisor of degree `n` (area SY). -/
  constMap : ∀ (n : ℕ) (E : Dv C K), E.IsEffective → Ddeg C K E = n →
    (X : Sch K) → (X ⟶ (symGeom n).S)
  /-- `divOf` of a constant map is the base change of the divisor (area SY). -/
  constMap_divOf : ∀ (n : ℕ) (E : Dv C K) (hE : E.IsEffective) (hd : Ddeg C K E = n)
    (X : Sch K) {F : Type u} [Field F] [Algebra K F] (p : FPt X F),
    (symGeom n).divOf (p ≫ constMap n E hE hd X) = bcKF F E
  /-- the identification `Sym¹ C = C` (area SY). -/
  curveIso : C.toOver ⟶ (symGeom 1).S
  /-- `divOf` of a point of `C` (area SY). -/
  curveIso_divOf : ∀ {F : Type u} [Field F] [Algebra K F] (x : FPt C.toOver F),
    (symGeom 1).divOf (x ≫ curveIso) = Work.SpecLin.ptDiv x
  /-- **The map `x ↦ x + E`** for an effective `K`-divisor `E` of degree `g - 1`
  (`g ≥ 1`), i.e. area `SY`'s `Sym.curveAdd` transported to the symmetric powers of this
  datum. -/
  curveAddOf : ∀ (g : ℕ), 1 ≤ g → (E : Dv C K) → E.IsEffective →
    Ddeg C K E = (g : ℤ) - 1 → (C.toOver ⟶ (symGeom g).S)
  /-- **The quotient property of `Symⁿ C`** (`SymQuotData.desc` for this family of symmetric
  powers): an `S_n`-invariant morphism `Cⁿ ⟶ Z` factors uniquely through the quotient map. -/
  desc : ∀ (n : ℕ) {Z : Sch K} (f : Work.SymQuot.prod C.toOver n ⟶ Z),
    (∀ σ : Equiv.Perm (Fin n), (Work.SymQuot.permIso C.toOver σ).hom ≫ f = f) →
    ∃! g : (symGeom n).S ⟶ Z,
      (symGeom n).powMap (fun m : Fin n => Work.SymQuot.proj C.toOver n m) ≫ g = f
  /-- `divOf` of `x + E`. -/
  curveAddOf_divOf : ∀ (g : ℕ) (hg : 1 ≤ g) (E : Dv C K) (hE : E.IsEffective)
    (hd : Ddeg C K E = (g : ℤ) - 1) {F : Type u} [Field F] [Algebra K F]
    (x : FPt C.toOver F),
    (symGeom g).divOf (x ≫ curveAddOf g hg E hE hd) = Work.SpecLin.ptDiv x + bcKF F E

namespace SYData

variable {C : Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
  {sg : ∀ n, Work.SpecLin.SymGeom C n} (sy : SYData C P0 sg)

/-- The divisor of a point of `Sym^n C`, for the symmetric powers of the data. -/
abbrev divOf (n : ℕ) {F : Type u} [Field F] [Algebra K F] (p : FPt (sg n).S F) :
    Dv C F := (sg n).divOf p

end SYData

/-! ## The `RESID`-side datum -/

/-- **The `resid_exists` field of `Work.GroupChunk.Input` as it is currently stated** (defect
D1 of the lead's closure design): RESID is demanded for *every* integral `X`, without the
`[IsLocallyNoetherian]` and the integral closedness of the stalks that the only RESID theorem on
disk (`Work.Domain.Resid.ResidData.exists_residMap`) needs.  Taken here as explicit data; after
the interface fix of area `GC` this becomes `Work.Domain.Resid.input_resid_exists` applied to
`ResidData.exists_residMap` with the two normality fields. -/
abbrev ResidOld (C : Curve K) [Work.SpecLin.DivBase C] (sg : ∀ n, Work.SpecLin.SymGeom C n)
    (g : ℕ) (hproper : ∀ n, IsProper ((sg n).S).hom) : Prop :=
  ∀ {X : Sch K} [IsIntegral X.left] [IsLocallyNoetherian X.left]
    (hX : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x)) (r m : ℕ)
    (a : X ⟶ (sg r).S) (b : X ⟶ (sg (r + m)).S), g ≤ m →
    ∃ σ : X.left ⤏ (sg m).S.left,
      Work.GroupChunk.Resid C sg (inferInstance : IsReduced X.left)
        (by haveI := hproper m; exact inferInstance) a b σ

variable {C : Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]

/-- **The `RESID` datum of `gcInput`, discharged by area `DM`.**  With the corrected interface of
area `GC` (`resid_exists` carrying `[IsLocallyNoetherian]` and the integral closedness of the
stalks, plus the two fields `normal_Sym`/`normal_SymSym`), the datum `ResidOld` is a *theorem*:
`Work.Domain.Resid.input_resid_exists` has exactly the corrected shape.  The two remaining
arguments are the invariance of `ℓ` under base change of the field (area `CB`,
`Work.GCBasics.DivBaseChange.pull_ell`) and SPEC-LIN (area `PR`, `Work.SpecLin.specLin`). -/
theorem residOld_of_input (D : GroupChunk.Input C P0)
    (ell_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
      (e : F →ₐ[K] F') (A : Dv C F), ell C (Work.SpecLin.DivBase.bc e A) = ell C A)
    (specLin : ∀ {n : ℕ} (G : Work.SpecLin.SymGeom C n) (R : Type u) [CommRing R] [IsDomain R]
      [ValuationRing R] [Algebra K R] (a b : Work.SpecLin.RPt G.S R),
      Work.SpecLin.LinEquiv C (G.divOf (Work.SpecLin.genPt R ≫ a))
        (G.divOf (Work.SpecLin.genPt R ≫ b)) →
      Work.SpecLin.LinEquiv C (G.divOf (Work.SpecLin.closedPt R ≫ a))
        (G.divOf (Work.SpecLin.closedPt R ≫ b))) :
    ResidOld C D.symGeom D.g D.isProper_Sym := by
  intro X _ _ hX r m a b hm
  exact Work.Domain.Resid.input_resid_exists (K := K) D ell_bc specLin hX r m a b hm

/-! ## C3: the `GroupChunk.Input` builder -/

variable {C : Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]

/-- Pullback of divisors agrees on the two presentations of the identity field extension. -/
theorem bc_ofId_eq (E : Dv C K) {F : Type u} [Field F] [Algebra K F] :
    Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) E = bcKF F E := by
  have h : IsScalarTower.toAlgHom K K F = Algebra.ofId K F :=
    AlgHom.ext fun x => by
      rw [IsScalarTower.toAlgHom_apply, Algebra.ofId_apply]
  rw [h]
  rfl

/-- Pullback of divisors commutes with the `ℕ`-multiples. -/
theorem bc_nsmul {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D : Dv C F) (n : ℕ) :
    Work.SpecLin.DivBase.bc e (n • D) = n • Work.SpecLin.DivBase.bc e D := by
  induction n with
  | zero => rw [zero_nsmul, Work.SpecLin.DivBase.bc_zero, zero_nsmul]
  | succ k ih => rw [succ_nsmul, Work.SpecLin.DivBase.bc_add, ih, succ_nsmul]

/-- **C3: the chart datum of area `GC` for a concrete curve.**  From

* the `SY`-side data (area `SY`/`BNChart`), the `RochData` `R` (area `RR`) and the
  Brill–Noether chart datum `cd` (area `CH`), together with
* the RESID datum (area `DM`) in the current shape of the interface, the `divOf`-identity for
  the base point (the divisor of `P₀` is the base divisor `P0Div`), and the integral closedness
  of the stalks of `Sym^g C` and `Sym^g C ⊗ Sym^g C` (area `NM`, the new normality fields),

we build `Work.GroupChunk.Input C P0`.  The genus `g` is `R.g`, the base divisor is
`[P₀] := ptDiv (P0Pt C P0 K)`, `curveAdd` is `Sym.curveAdd` at `(g-1) • [P₀]`, and the chart
fields (`V`, `ell_eq_one_of_landsIn`, `Idx`, `fintype`, `E`, `cov`) are those of `cd`. -/
def gcInput {sg : ∀ n, Work.SpecLin.SymGeom C n} (sy : SYData C P0 sg)
    (R : Work.Charts.RochData C) [NeZero R.g]
    (cd : @Work.Charts.ChartDatum K _ C _ R (sg R.g) P0)
    (hresid : ResidOld C sg R.g sy.isProper_Sym)
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra K F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 K)))
    (hnorm_g : ∀ x : ((sg R.g).S).left,
      IsIntegrallyClosed (((sg R.g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((sg R.g).S) ⊗ ((sg R.g).S)).left,
      IsIntegrallyClosed ((((sg R.g).S) ⊗ ((sg R.g).S)).left.presheaf.stalk x)) :
    GroupChunk.Input C P0 := by
  letI : Work.SpecLin.SymGeom C R.g := sg R.g
  have hg : 1 ≤ R.g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne R.g)
  let E₀ : Dv C K := Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 K)
  have hE₀eff : E₀.IsEffective := Work.SpecLin.ptDiv_isEffective _
  have hE₀deg : Ddeg C K E₀ = 1 := Work.SpecLin.Points.ptDiv_deg _
  have hEeff : ((R.g - 1) • E₀).IsEffective := by
    intro Q
    rw [Finsupp.nsmul_apply]
    exact mul_nonneg (Nat.cast_nonneg _) (hE₀eff Q)
  have hEdeg : Ddeg C K ((R.g - 1) • E₀) = (R.g : ℤ) - 1 := by
    rw [map_nsmul, hE₀deg, nsmul_eq_mul, mul_one]
    omega
  have hcurve : ∀ {F : Type u} [Field F] [Algebra K F] (x : FPt C.toOver F),
      (sg R.g).divOf (x ≫ sy.curveAddOf R.g hg ((R.g - 1) • E₀) hEeff hEdeg)
        = Work.SpecLin.ptDiv x + (R.g - 1) • bcKF F E₀ := by
    intro F _ _ x
    rw [sy.curveAddOf_divOf]
    congr 1
    show Work.SpecLin.DivBase.bc (Algebra.ofId K F) ((R.g - 1) • E₀)
      = (R.g - 1) • Work.SpecLin.DivBase.bc (Algebra.ofId K F) E₀
    exact bc_nsmul (Algebra.ofId K F) E₀ (R.g - 1)
  exact
    { g := R.g
      symGeom := sg
      isProper_Sym := sy.isProper_Sym
      geomIntegral_Sym := sy.geomIntegral_Sym
      geomIrred_Sym := sy.geomIrred_Sym
      locallyOfFiniteType_Sym := sy.locallyOfFiniteType_Sym
      addMap := sy.addMap
      addMap_divOf := sy.addMap_divOf
      constMap := sy.constMap
      constMap_divOf := sy.constMap_divOf
      curveIso := sy.curveIso
      curveIso_divOf := sy.curveIso_divOf
      P0Div := E₀
      P0Div_isEffective := hE₀eff
      P0Div_deg := hE₀deg
      P0Div_ptDiv := hP0Div
      curveAdd := sy.curveAddOf R.g hg ((R.g - 1) • E₀) hEeff hEdeg
      curveAdd_divOf := hcurve
      ell_zero := Work.Charts.ell_zero C
      rr7 := Work.JacFinal.rr7_of_rochData R
      V := cd.V
      ell_eq_one_of_landsIn := cd.ell_eq_one_of_landsIn
      Idx := cd.ι
      fintype := cd.fintype
      E := cd.E
      cov := by
        intro F _ _ c
        obtain ⟨i, y, hy, hc⟩ := cd.cov c
        refine ⟨i, y, hy, ?_⟩
        have hE : RPt.map (IsScalarTower.toAlgHom K K F) (cd.E i)
            = RPt.map (Algebra.ofId K F) (cd.E i) := by
          rw [show IsScalarTower.toAlgHom K K F = (Algebra.ofId K F : K →ₐ[K] F) from
            AlgHom.ext fun x => by
              rw [IsScalarTower.toAlgHom_apply, Algebra.ofId_apply]]
        rw [hE] at hc
        exact hc
      resid_exists := hresid
      normal_Sym := hnorm_g
      normal_SymSym := hnorm_gg }

/-! ## C4: the `Universal.Input` builder -/

/-- **C4, first part: the quotient property of area `SY` for the symmetric powers of `SYData`**,
i.e. `Work.Universal.SymQuotData` for the chart datum built by `gcInput`. -/
theorem symQuotData {sg : ∀ n, Work.SpecLin.SymGeom C n} (sy : SYData C P0 sg)
    (R : Work.Charts.RochData C) [NeZero R.g]
    (cd : @Work.Charts.ChartDatum K _ C _ R (sg R.g) P0)
    (hresid : ResidOld C sg R.g sy.isProper_Sym)
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra K F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 K)))
    (hnorm_g : ∀ x : ((sg R.g).S).left,
      IsIntegrallyClosed (((sg R.g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((sg R.g).S) ⊗ ((sg R.g).S)).left,
      IsIntegrallyClosed ((((sg R.g).S) ⊗ ((sg R.g).S)).left.presheaf.stalk x)) :
    @Work.Universal.SymQuotData K _ C P0 _ (gcInput sy R cd hresid hP0Div hnorm_g hnorm_gg) :=
  { desc := fun n Z f hf => sy.desc n f hf }

open scoped MonObj

section UP

variable (D : GroupChunk.Input C P0) [htc : Work.Universal.SymQuotData C P0 D]

/-- **The key lemma of area `KL` in the divisor form of area `UP`** (`Work.Universal.Input.kl`
and `kl_add`), for a fixed chart datum and its quotient property: `Σ f` is constant on linear
equivalence classes of effective divisors of the same degree, and additive on sums.

The adapter from area `KL`'s model form to this statement is area `CurveFacts`'s A6.
`Work.JacClose.upInput` consumes exactly this structure. -/
structure KLLemma : Prop where
  /-- `Σ f` is constant on linear equivalence classes of effective divisors of the same degree. -/
  kl : ∀ {A : Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom] (f : C.toOver ⟶ A)
    {F : Type u} [Field F] [Algebra K F] (E E' : Dv C F) (hE : E.IsEffective)
    (hE' : E'.IsEffective) (n : ℕ)
    (hn : Ddeg C F E = (n : ℤ)) (hn' : Ddeg C F E' = (n : ℤ)), LinEquiv C E E' →
    Work.Universal.sumDiv D f E hE n hn = Work.Universal.sumDiv D f E' hE' n hn'
  /-- `Σ f` is additive on sums of effective divisors. -/
  kl_add : ∀ {A : Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom] (f : C.toOver ⟶ A)
    {F : Type u} [Field F] [Algebra K F] (E E' : Dv C F) (hE : E.IsEffective) (hE' : E'.IsEffective)
    (n m : ℕ) (hn : Ddeg C F E = (n : ℤ)) (hm : Ddeg C F E' = (m : ℤ))
    (hEE' : (E + E').IsEffective),
    Work.Universal.sumDiv D f (E + E') hEE' (n + m) (Work.Universal.ddeg_add hn hm) =
      Work.Universal.sumDiv D f E hE n hn * Work.Universal.sumDiv D f E' hE' m hm

end UP

/-- **C4, the `Universal.Input` of area `UP` from the outputs of the areas.**  The `GC` outputs
(the glued group chunk, its group law, the universal property of the gluing, the Abel–Jacobi
maps `AJ₀` and `AJSym` with their defining properties, properness, geometric integrality and
separatedness) are the outputs of area `GC`; the quotient property of `Symⁿ C` is area `SY`'s;
the key lemma is `KLLemma`. -/
def upInputCore {D : GroupChunk.Input C P0} [htc : Work.Universal.SymQuotData C P0 D]
    (h : @KLLemma K _ C P0 _ D htc) :
    @Work.Universal.Input K _ C P0 _ D := by
  letI : GroupChunk.Input C P0 := D
  exact
    { desc := htc.desc
      glued := D.toGlued
      grpObj := Work.GroupChunk.Input.instGrpObj D
      isProper_G := Work.GroupChunk.instIsProper_G D
      geomIntegral_G := Work.GroupChunk.instGeometricallyIntegral_G D
      isSeparated_G := Work.GroupChunk.instIsSeparated_G D
      descG := fun {Y} φ hφ => Work.GroupChunk.Desc.desc_exists φ hφ
      AJ₀ := Work.GroupChunk.Input.AJ₀ D
      AJ₀_pt := Work.GroupChunk.Input.AJ₀_pt D
      AJSym := Work.GroupChunk.Input.AJSym D
      AJSym_powMap := fun {T} x => Work.GroupChunk.Input.AJSym_powMap D x
      AJSym_surjective := Work.GroupChunk.Input.AJSym_surjective D
      cls_AJ₀ := fun {F} _ _ x => Work.GroupChunk.Input.cls_AJ₀ D x
      P0Div_ptDiv := D.P0Div_ptDiv
      kl := h.kl
      kl_add := h.kl_add }

/-- **C4: the package of area `UP` for the chart datum of `gcInput`.**  This is `upInputCore`
applied to the builder `gcInput` of C3 and to area `SY`'s quotient property `symQuotData`; the
key lemma is taken as the explicit datum `h`, since its adapter to the `sumDiv`-form is area
`CurveFacts`'s A6. -/
def upInput {sg : ∀ n, Work.SpecLin.SymGeom C n} (sy : SYData C P0 sg)
    (R : Work.Charts.RochData C) [NeZero R.g]
    (cd : @Work.Charts.ChartDatum K _ C _ R (sg R.g) P0)
    (hresid : ResidOld C sg R.g sy.isProper_Sym)
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra K F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 K)))
    (hnorm_g : ∀ x : ((sg R.g).S).left,
      IsIntegrallyClosed (((sg R.g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((sg R.g).S) ⊗ ((sg R.g).S)).left,
      IsIntegrallyClosed ((((sg R.g).S) ⊗ ((sg R.g).S)).left.presheaf.stalk x))
    (h : @KLLemma K _ C P0 _ (gcInput sy R cd hresid hP0Div hnorm_g hnorm_gg)
      (symQuotData sy R cd hresid hP0Div hnorm_g hnorm_gg)) :
    @Work.Universal.Input K _ C P0 _
      (gcInput sy R cd hresid hP0Div hnorm_g hnorm_gg) :=
  @upInputCore K _ C P0 _
    (gcInput sy R cd hresid hP0Div hnorm_g hnorm_gg)
    (symQuotData sy R cd hresid hP0Div hnorm_g hnorm_gg) h


end

end Work.JacClose
