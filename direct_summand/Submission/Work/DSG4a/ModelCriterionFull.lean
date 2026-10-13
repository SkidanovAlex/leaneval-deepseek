import Mathlib
import Submission.Work.DSG4a.Data
import Submission.Work.DSG4a.cechHomology_finite_isZero
import Submission.Work.DSG4a.exists_model_of_bounded_homology
import Submission.Work.DSG4a.ModelCriterion
import Submission.Work.DSEQ0.exists_lift_of_quasiIso

/-!
# DSG4a — the model criterion with *all* its data

`Work.DSG4a.exists_model_criterion` (in `ModelCriterion.lean`) already produces, from the output
of the areas `F1` and `COH`, a finite free K-projective model `P`, a coaugmentation `cc` and the
criterion `IsSplitMono (rgUnit A X f) ↔ IsUnimodular A (modelElem P cc)`.

The base-change half of the local-to-global argument also needs, however, the *quasi-isomorphism*
`q : P ⟶ cechZ A X f U`, the lift of the Čech coaugmentation along it, and the `F1` isomorphism
`e₀` with its compatibility clause (all of which are used on the base-changed side, where the
model of the base-changed Čech complex is `baseChangeComplex P` and its coaugmentation is a lift
along `baseChangeComplexFunctor.map q ≫ Φ`).

This file therefore restates the criterion returning the whole tuple.  Nothing new is proved —
the proof is the one of `exists_model_criterion` with the intermediate data exported.
-/

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- **The model criterion of area `G4a`, with all the data.**  From the output `F1Data A X f U`
of the area `F1` and the output `CohData A X f` of the area `COH` (for a finite family of opens
`U`), there are

* a bounded-above complex `P` of finitely generated free `A`-modules and a quasi-isomorphism
  `q : P ⟶ cechZ A X f U`,
* the Čech coaugmentation `ccAn` of `F1` and a lift `cc` of it along `q` in the derived
  category,
* the isomorphism `e₀` of `F1` and its compatibility clause `he₀`,

such that `IsSplitMono (rgUnit A X f) ↔ Module.IsUnimodular A (modelElem P cc)`. -/
theorem exists_model_criterion_full {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hF1 : F1Data A X f U) (hCoh : CohData A X f) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (cc : singleZ A ⟶ P)
      (q : P ⟶ DSMap.cechZ A X f U) (ccAn : singleZ A ⟶ DSMap.cechZ A X f U)
      (e₀ : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
        DerivedCategory.Q.obj (DSMap.cechZ A X f U)),
      IsFreeModel A P ∧ QuasiIso q ∧ coaugClause X f U ccAn ∧
      (DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e₀.hom =
        Criterion.unitComparison A (DSMap.cechZ A X f U) ccAn) ∧
      (DerivedCategory.Q.map ccAn = DerivedCategory.Q.map cc ≫ DerivedCategory.Q.map q) ∧
      (IsSplitMono (DSMap.rgUnit A X f) ↔ Module.IsUnimodular A (Criterion.modelElem P cc)) := by
  obtain ⟨ccAn, e₀, hccAn, he₀⟩ := hF1
  obtain ⟨N, hN⟩ := cechHomology_finite_isZero (DSMap.cechZ A X f U) e₀ hCoh
  have hfin : ∀ i : ℤ, Module.Finite A ((DSMap.cechZ A X f U).homology i) := fun i => (hN i).1
  have hcast : ((((max N 0).toNat : ℕ) : ℤ)) = max N 0 :=
    Int.toNat_of_nonneg (le_max_right N 0)
  have hzero : ∀ i : ℤ, (((max N 0).toNat : ℕ) : ℤ) < i →
      IsZero ((DSMap.cechZ A X f U).homology i) := by
    intro i hi
    refine (hN i).2 ?_
    rw [hcast] at hi
    exact lt_of_le_of_lt (le_max_left N 0) hi
  obtain ⟨P, q, hPfin, hPfree, hPbdd, hq⟩ :=
    Work.DSG4a.exists_model_of_bounded_homology (DSMap.cechZ A X f U) (max N 0).toNat hfin hzero
  have hP : IsFreeModel A P := ⟨hPfin, hPfree, ⟨_, hPbdd⟩⟩
  haveI : CochainComplex.IsKProjective P := hP.isKProjective
  obtain ⟨cc, hcc⟩ := Work.DSEQ0.exists_lift_of_quasiIso P (DSMap.cechZ A X f U) q hq ccAn
  exact ⟨P, cc, q, ccAn, e₀, hP, hq, hccAn, he₀, hcc,
    isSplitMono_iff_isUnimodular_of_lift P q hq ccAn e₀ he₀ cc hcc⟩

end Work.DSG4a
