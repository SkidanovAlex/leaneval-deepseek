import Mathlib
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Serre.MVCohRatDefs
import Submission.Work.Serre.MVShift.ShQ
import Submission.Work.Serre.mvDeltaAuxDefs
import Submission.Work.Serre.mvDeltaAuxCupNat
import Submission.Work.Serre.mvDeltaAuxCupHom
import Submission.Work.Serre.mvDeltaAuxAssembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre

/-- **The rational Mayer–Vietoris connecting map is a derivation for the mixed cup product.**

For an open cover `X = U ∪ V`, a global relative class `U₀ ∈ H^{n₀}(X,A;ℚ)` and a class
`x ∈ H^m(U ∩ V; ℚ)` (absolute, on the overlap), the connecting map `δ` of the rational relative
Mayer–Vietoris sequence commutes with the cup product with `U₀`:

`(δ_∅ x) ⌣ U₀ = cast (δ_A (x ⌣ U₀|_{U∩V}))`,

where `δ_T = Work.Serre.mvDelta X T U V …` is the connecting map of the pair `(X,T)` and `⌣` is
`Work.Thom.mixedCupC`. This is the `(DELTA)` square of `Submission/Work/Serre/MVGLUE_SESSION7.md`
and the key input of the local-to-global gluing of the cup map
(`Work.Serre.MVGlue.glueCupIso`); it is a statement of pure homological algebra, independent of any
fibration. See `Submission/Work/Serre/MVDELTA_PLAN.md` for a route (the ℤ analogue
`Work.Thom.honestDelta_mixedCupFinal` is proved at the chain level; the file
`Submission/Work/Serre/mvDeltaCupMixed.lean` reduces the statement to the explicit comparison
`thetaRel`, via `mvDeltaCupMixed_of_thetaRel`, so it suffices to prove the `thetaRel`/`DiscPair`
instance `Work.Serre.DiscPair.mvDelta`-version, which is the only remaining gap). -/
theorem mvDeltaCupMixedAux (X : TopCat) (A : Set X) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (m : ℕ) (x : Work.Serre.mvCohUV X (∅ : Set X) U V m) :
    (Work.Thom.mixedCupC ℚ A (m + 1) n₀)
        ((Work.Thom.relToAbs ℚ (∅ : Set X) (m + 1)).hom
          ((Work.Serre.mvDelta X (∅ : Set X) U V hU hV hcov m).hom x)) U₀
      = (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
            (by omega : (m + n₀) + 1 = (m + 1) + n₀))).hom
          ((Work.Serre.mvDelta X A U V hU hV hcov (m + n₀)).hom
            ((Work.Thom.mixedCupC ℚ {y : ↥(U ∩ V) | (y : X) ∈ A} m n₀)
              ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) m).hom x)
              ((Work.Thom.relCohMap
                (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
                {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀))) := by
  obtain ⟨t, ht, rfl⟩ := Work.Cohomology.exists_relClassOf ℚ X A n₀ U₀
  show (Work.Thom.mixedCupC ℚ A (m + 1) n₀)
        ((Work.Thom.relToAbs ℚ (∅ : Set X) (m + 1)).hom
          ((Work.Serre.mvDelta X (∅ : Set X) U V hU hV hcov m).hom x))
        (Work.Cohomology.relClassOf ℚ X A t ht)
      = (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
            (by omega : (m + n₀) + 1 = (m + 1) + n₀))).hom
          ((Work.Serre.mvDelta X A U V hU hV hcov (m + n₀)).hom
            ((Work.Thom.mixedCupC ℚ (Work.Cohomology.interAU A (U ∩ V)) m n₀)
              ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) m).hom x)
              ((Work.Thom.relCohMap
                (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
                (Work.Cohomology.interAU A (U ∩ V)) A (fun _ hy => hy) ℚ n₀).hom
                (Work.Cohomology.relClassOf ℚ X A t ht))))
  obtain ⟨h1, h1V, h2, h2V⟩ := mvDeltaAuxCupNat X A U V n₀ t ht
  have hHomX : CupHomStatement X A n₀ t ht := mvDeltaAuxCupHom X A n₀ t ht
  have hHomUV : CupHomStatement (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
      (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht) :=
    mvDeltaAuxCupHom (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)) n₀
      (cupTgtUV X A U V n₀ t) (cupTgtUV_cocycle X A U V n₀ t ht)
  have hmor := deltaSquare X A U V hU hV hcov n₀ t ht h1 h1V h2 h2V hHomX hHomUV m
  rw [← U₀ovl_eq_relCohMap X A U V n₀ (Work.Cohomology.relClassOf ℚ X A t ht)]
  rw [ovlClass_relClassOf X A U V n₀ t ht]
  exact congrArg (fun f => ModuleCat.Hom.hom f x) hmor

end Work.Serre
