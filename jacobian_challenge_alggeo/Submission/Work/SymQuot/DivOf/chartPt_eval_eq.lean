/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The value of an invariant function at a point of `Symⁿ C` (area SY, `divOf`)

The *key lemma* of the `divOf` construction (`Work.SymQuot.DivOf.ChartPt.φ_eq_evalMap` in
`Submission/Work/SymQuot/NOTES.md`): for a point `p : Spec F ⟶ Symⁿ C` lying in the chart of an
affine open `V ⊆ C` (`d : ChartPt C n p`) and a lift `x : Fin n → C(F')` of `p` over a field
extension `F' ⊇ F` landing in `Vⁿ ⊆ Cⁿ`, the value of an `Sₙ`-invariant function `a` on `Vⁿ` at
the chart point `p` (i.e. `algebraMap F F' (d.φ a)`) equals its value at `x` (i.e. `d.evalMap x h a`).

The proof compares the two morphisms `Spec F' ⟶ Spec A` (`A` the chart ring) obtained

* by pulling `d.q` back along `Spec F' ⟶ Spec F`, and
* by restricting the lifted point `Π x_m : Spec F' ⟶ Cⁿ` to the chart `Spec A` of `Vⁿ`,

and uses that the chart inclusion `Spec A ⟶ Symⁿ C` is a monomorphism (an open immersion) together
with the factoring `d.q ≫ chartι = p.left` of the point through the chart and
`Sym.quot`'s restriction to the chart (`QuotientData.quotientMap_chartι`).
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.ChartPt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

/-- The value of the chart map `U ⟶ Spec Γ(X,U)^G` on a section: applying the chart map to an
invariant section `a` (transported to a section of `Spec Γ(X,U)^G` along `ΓSpecIso`) is the
restriction of `a` to the open subscheme `U`, transported along `ΓSpecIso`. -/
lemma chartMap_appTop_apply {G : Type u} [Group G] {X : Scheme.{u}} (A : GAction G X)
    (U : X.Opens) (hU : A.IsInvariantOpen U) (a : ↥(A.invariants U hU)) :
    (A.chartMap U hU).appTop ((Scheme.ΓSpecIso (GAction.chartRing A U hU)).inv.hom a) =
      U.topIso.inv ↑a := by
  have key : (A.chartMap U hU).appTop =
      (Scheme.ΓSpecIso (GAction.chartRing A U hU)).hom ≫
        CommRingCat.ofHom (A.invariants U hU).subtype ≫ U.topIso.inv := by
    rw [GAction.chartMap, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality_assoc]
  rw [key]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rw [CommRingCat.comp_apply]
  rfl

/-- The sections over an open `U ⊆ Y` of a morphism `φ : X ⟶ Y` whose image lies in `U` are
obtained by restricting the sections over `U` to the open subscheme `U` and then pulling back
along the factorisation `X ⟶ U ⟶ Y` of `φ`. -/
lemma appLE_of_comp {X Y : Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens)
    (h : (⊤ : X.Opens) ≤ (TopologicalSpace.Opens.map φ.base).obj U)
    (g : X ⟶ U.toScheme) (hg : g ≫ U.ι = φ) :
    φ.appLE U ⊤ h = U.topIso.inv ≫ g.appTop := by
  subst hg
  rw [← Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ (by simp) (by simp)]
  rw [show U.ι.appLE U ⊤ _ = U.topIso.inv from by
        rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]; congr 1]
  rw [show g.appLE ⊤ ⊤ _ = g.appTop from Scheme.Hom.appLE_eq_app g]

theorem chartPt_eval_eq {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : Work.SymQuot.DivOf.ChartPt C n p)
    {F' : Type u} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    (x : Fin n → Work.SpecLin.CurveFPt C F')
    (hx : Work.SymQuot.Sym.powMap C n x = Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p)
    (h : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of F')).Opens) ≤
      (TopologicalSpace.Opens.map ((CategoryTheory.Limits.Pi.lift x :
        Work.SpecLin.specOf (K := K) F' ⟶ Work.SymQuot.prod C.toOver n)).left.base).obj d.openOf)
    (a : ↥d.chartRingOf) :
    algebraMap F F' (d.φ a) = d.evalMap x h ↑a := by
  let e : F →ₐ[K] F' := IsScalarTower.toAlgHom K F F'
  have hx' : Work.SymQuot.Sym.powMap C n x = Work.SpecLin.RPt.map e p := hx
  -- the chart of `Vⁿ` containing `p`
  let U : (Work.SymQuot.symData C n).Chart :=
    ⟨d.openOf, Work.SymQuot.Prod.isAffineOpen_piOpen C.toOver n d.V d.isAffineOpen_V,
      Work.SymQuot.DivOf.symPiOpen_invariant C n d.V⟩
  have hfac : d.q ≫ (Work.SymQuot.symData C n).chartι U = p.left := d.fac
  -- the lift of `Π x_m` to the open subscheme `Vⁿ`
  have hH' : Set.range ⇑((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F' ⟶
        Work.SymQuot.prod C.toOver n)).left ⊆ Set.range ⇑d.openOf.ι := by
    rw [Scheme.Opens.range_ι]
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact h (x := z) trivial
  let g : Spec (CommRingCat.of F') ⟶ d.openOf.toScheme :=
    IsOpenImmersion.lift d.openOf.ι ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F' ⟶
      Work.SymQuot.prod C.toOver n)).left hH'
  have hg : g ≫ d.openOf.ι = ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F' ⟶
      Work.SymQuot.prod C.toOver n)).left := IsOpenImmersion.lift_fac _ _ hH'
  -- the two morphisms `Spec F' ⟶ Spec A` agree, because their composites with the (mono) chart
  -- inclusion both equal `Sym.powMap x`
  have hσ : g ≫ (Work.SymQuot.symAction C n).chartMap d.openOf
        (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V)
      = (Work.SpecLin.specOfMap e).left ≫ d.q := by
    apply (cancel_mono ((Work.SymQuot.symData C n).chartι U)).mp
    have key1 : (Work.SymQuot.symAction C n).chartMap d.openOf
          (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V) ≫ (Work.SymQuot.symData C n).chartι U
        = d.openOf.ι ≫ (Work.SymQuot.symData C n).quotientMap :=
      (Work.SymQuot.QuotientData.quotientMap_chartι (Work.SymQuot.symData C n) U).symm
    have hpow : (Work.SymQuot.Sym.powMap C n x).left
        = ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F' ⟶
            Work.SymQuot.prod C.toOver n)).left ≫ (Work.SymQuot.symData C n).quotientMap := by
      simp only [Work.SymQuot.Sym.powMap, Work.SymQuot.Sym.quot_left, Over.comp_left]
    calc (g ≫ (Work.SymQuot.symAction C n).chartMap d.openOf
            (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V)) ≫ (Work.SymQuot.symData C n).chartι U
        = g ≫ ((Work.SymQuot.symAction C n).chartMap d.openOf
            (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V) ≫ (Work.SymQuot.symData C n).chartι U) :=
          Category.assoc _ _ _
      _ = g ≫ (d.openOf.ι ≫ (Work.SymQuot.symData C n).quotientMap) := by rw [key1]
      _ = (g ≫ d.openOf.ι) ≫ (Work.SymQuot.symData C n).quotientMap := (Category.assoc _ _ _).symm
      _ = (Work.SymQuot.Sym.powMap C n x).left := by rw [hg, hpow]
      _ = (Work.SpecLin.RPt.map e p).left := by rw [hx']
      _ = (Work.SpecLin.specOfMap e).left ≫ p.left := by
            simp only [Work.SpecLin.RPt.map, Over.comp_left]
      _ = ((Work.SpecLin.specOfMap e).left ≫ d.q) ≫ (Work.SymQuot.symData C n).chartι U := by
            rw [Category.assoc, hfac]
  -- the value of `evalMap` at `a` is the value of `σ` at `a`
  have hmain : d.evalMap x h ↑a =
      (Scheme.ΓSpecIso (CommRingCat.of F')).hom.hom
        ((g ≫ (Work.SymQuot.symAction C n).chartMap d.openOf
            (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V)).appTop
          ((Scheme.ΓSpecIso (GAction.chartRing (Work.SymQuot.symAction C n) d.openOf
            (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V))).inv.hom a)) := by
    rw [ChartPt.evalMap, RingHom.comp_apply]
    rw [appLE_of_comp ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F' ⟶
      Work.SymQuot.prod C.toOver n)).left d.openOf h g hg]
    rw [CommRingCat.hom_comp]
    first
      | rw [RingHom.comp_apply]
      | dsimp only
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [chartMap_appTop_apply]
    rfl
  -- the value of `φ` at `a` in the explicit form
  have hphi : d.φ a = (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
        (d.q.appTop ((Scheme.ΓSpecIso (GAction.chartRing (Work.SymQuot.symAction C n) d.openOf
          (Work.SymQuot.DivOf.symPiOpen_invariant C n d.V))).inv.hom a)) := by
    rw [ChartPt.φ]
    rfl
  -- assemble
  rw [hmain, hσ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [show (Work.SpecLin.specOfMap e).left
      = Spec.map (CommRingCat.ofHom e.toRingHom) from by
        simp only [Work.SpecLin.specOfMap, Work.SpecLin.specOfMapHom, Over.homMk_left]]
  conv_rhs => rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
  rw [hphi]
  rfl

end Work.SymQuot.DivOf
