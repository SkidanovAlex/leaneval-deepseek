import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.PtOfChartHom
import Submission.Work.SymQuot.DivOf.Complete.evalAlg_coordPullbackAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 2000000

universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry

/-! ## Two general lemmas used in the computation

We record the two "spec ↔ sections" compatibilities that turn the ring map `chartEval`
into the morphism `Π_m y_m` of schemes.
-/

/-- For an affine open `U ⊆ X` and `f : Spec R ⟶ X` whose image lies in `U`, the `Spec` of the
ring map obtained by pulling back sections along `f` and identifying `Γ(Spec R) ≅ R` is a
section of `f` along the canonical immersion `Spec Γ(X,U) ⟶ X`: precomposing it with that
immersion gives back `f`. -/
private theorem Spec_map_appLE_SpecIso_fromSpec {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : Spec R ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ f ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso R).hom.hom.comp (f.appLE U ⊤ h).hom)) ≫
        hU.fromSpec = f := by
  have h1 : CommRingCat.ofHom ((Scheme.ΓSpecIso R).hom.hom.comp (f.appLE U ⊤ h).hom)
      = (f.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso R).hom := by
    rw [show (Scheme.ΓSpecIso R).hom.hom.comp (f.appLE U ⊤ h).hom
      = ((f.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso R).hom).hom from rfl, CommRingCat.ofHom_hom]
  rw [h1, Spec.map_comp, Category.assoc]
  rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU (isAffineOpen_top (Spec R)) h]
  rw [IsAffineOpen.fromSpec_top]
  rw [← Scheme.isoSpec_Spec_hom R]
  rw [Iso.hom_inv_id_assoc]

/-- For a chart `U` of the quotient data `D`, the inclusion of the invariants
`Γ(X,U)^Γ ↪ Γ(X,U)`, read on spectra, followed by the inclusion of the chart into the
quotient, is the canonical immersion `Spec Γ(X,U) ⟶ X` followed by the quotient map:
this is the restriction of the defining factorisation of the quotient map to the chart. -/
private theorem subtype_chartι {Γ : Type u} [Group Γ] [Fintype Γ] {X : Scheme.{u}}
    (D : Work.SymQuot.QuotientData Γ X) (U : D.Chart) :
    Spec.map (CommRingCat.ofHom (Subring.subtype (D.action.invariants U.1 U.2.2))) ≫ D.chartι U
      = U.2.1.fromSpec ≫ D.quotientMap := by
  have h := D.quotientMap_chartι U
  have hmap : D.action.chartMap U.1 U.2.2 =
      U.1.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (Subring.subtype (D.action.invariants U.1 U.2.2))) := rfl
  rw [hmap, Category.assoc] at h
  rw [← IsAffineOpen.isoSpec_inv_ι U.2.1]
  rw [Category.assoc, h, ← Category.assoc, ← Category.assoc]
  rw [show U.1.toSpecΓ = U.2.1.isoSpec.hom from rfl, Iso.inv_hom_id, Category.id_comp]

open CategoryTheory Limits AlgebraicGeometry in
/-- **The point of `Symⁿ C` defined by the chart ring map `chartEval` is the sum of the points
`y`.**

Both sides are morphisms `Spec L ⟶ Symⁿ C`, so it suffices to compare their underlying morphisms
of schemes.  The ring map `chartEval = evalAlg ∘ subtype` splits as the pullback of sections
along `Π_m y_m` (giving `Spec L ⟶ Spec Γ(Cⁿ,Vⁿ)`, which is `Π_m y_m` composed with the
immersion `Spec Γ(Cⁿ,Vⁿ) ⟶ Cⁿ`) followed by the inclusion of the invariants.  Applying it to
the defining factorisation `U.ι ≫ quotientMap = chartMap U ≫ chartι U` of the quotient map on
the chart `U = Vⁿ` yields the claim. -/
theorem ptOfChartHom_evalAlg {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {L : Type u} [Field L] [Algebra K L]
    {V : C.left.Opens} (hV : IsAffineOpen V) (y : Fin n → Work.SpecLin.CurveFPt C L)
    (h : ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) L ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n)
    (hΦ : ∀ k : K, chartEval C n y h (chartConst C n (chartOf C n hV) k) = algebraMap K L k) :
    ptOfChartHom C n hV (chartEval C n y h) hΦ =
      Work.SymQuot.Sym.powMap C n y := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (chartEval C n y h)) ≫
      (Work.SymQuot.symData C n).chartι (chartOf C n hV) =
    (Limits.Pi.lift y).left ≫ (Work.SymQuot.symData C n).quotientMap
  -- `chartEval` is the composite of `evalAlg` with the inclusion of the invariants.
  rw [show Spec.map (CommRingCat.ofHom (chartEval C n y h))
      = Spec.map (CommRingCat.ofHom (evalAlg C V n y h)) ≫
        Spec.map (CommRingCat.ofHom (Subring.subtype (Work.SymQuot.chartInvariants (C := C)
          (n := n) (Work.SymQuot.piOpen C.toOver V n)
          (Work.SymQuot.DivOf.symPiOpen_invariant C n V)))) from by
    rw [show chartEval C n y h = (evalAlg C V n y h).comp (Subring.subtype
        (Work.SymQuot.chartInvariants (C := C) (n := n) (Work.SymQuot.piOpen C.toOver V n)
          (Work.SymQuot.DivOf.symPiOpen_invariant C n V))) from rfl,
      CommRingCat.ofHom_comp, Spec.map_comp]]
  rw [Category.assoc]
  -- The inclusion of the invariants, followed by the chart inclusion, is the immersion of `Vⁿ`
  -- followed by the quotient map.
  rw [show Spec.map (CommRingCat.ofHom (Subring.subtype (Work.SymQuot.chartInvariants (C := C)
        (n := n) (Work.SymQuot.piOpen C.toOver V n)
        (Work.SymQuot.DivOf.symPiOpen_invariant C n V)))) ≫
        (Work.SymQuot.symData C n).chartι (chartOf C n hV)
      = (chartOf C n hV).2.1.fromSpec ≫ (Work.SymQuot.symData C n).quotientMap from
    subtype_chartι (Work.SymQuot.symData C n) (chartOf C n hV)]
  rw [← Category.assoc]
  -- `evalAlg` is the pullback of sections along `Π_m y_m`.
  rw [show Spec.map (CommRingCat.ofHom (evalAlg C V n y h)) ≫ (chartOf C n hV).2.1.fromSpec
      = (Limits.Pi.lift y).left from
    Spec_map_appLE_SpecIso_fromSpec (Limits.Pi.lift y).left (chartOf C n hV).2.1 h]

end Work.SymQuot.DivOf.Complete
