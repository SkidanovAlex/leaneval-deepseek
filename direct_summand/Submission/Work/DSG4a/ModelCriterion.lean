import Mathlib
import Submission.Work.DSG4a.Data
import Submission.Work.DSG4a.cechHomology_finite_isZero
import Submission.Work.DSG4a.exists_model_of_bounded_homology
import Submission.Work.DSEQ0.exists_lift_of_quasiIso

/-!
# DSG4a — the model criterion, from the areas `F1` and `COH`

This file combines the pieces of the area `G4a` that do not involve base change: the output
`F1Data A X f U` of the frozen area `F1`, the output `CohData A X f` of the frozen area `COH`,
the transport of finiteness/boundedness of the cohomology from `RΓ(X,𝒪_X)` to the Čech complex
`cechZ A X f U` (`Work.DSG4a.cechHomology_finite_isZero`), the construction of a bounded-above
complex `P` of finitely generated free `A`-modules quasi-isomorphic to it
(`Work.DSG4a.exists_model_of_bounded_homology`), and the lift of the Čech coaugmentation along
that quasi-isomorphism (`Work.DSEQ0.exists_lift_of_quasiIso`).

The result `exists_model_criterion` is the hypothesis `hcrit` of
`Work.DSG4a.area_G4a_localGlobal_of_models`: `IsSplitMono (rgUnit A X f)` is equivalent to the
unimodularity of the model element `modelElem P cc`.
-/

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- **The model criterion of area `G4a`, from the areas `F1` and `COH`.**  For a finite family of
opens `U` covering `X`, given the output `F1Data A X f U` of the area `F1` and the output
`CohData A X f` of the area `COH`, there are a bounded-above complex `P` of finitely generated
free `A`-modules and a coaugmentation `cc : A[0] ⟶ P` such that

`IsSplitMono (rgUnit A X f) ↔ Module.IsUnimodular A (modelElem P cc)`.

This is the hypothesis `hcrit` of `Work.DSG4a.area_G4a_localGlobal_of_models`. -/
theorem exists_model_criterion {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hF1 : F1Data A X f U) (hCoh : CohData A X f) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (cc : singleZ A ⟶ P),
      IsFreeModel A P ∧
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
  exact ⟨P, cc, hP, isSplitMono_iff_isUnimodular_of_lift P q hq ccAn e₀ he₀ cc hcc⟩

end Work.DSG4a
