import Mathlib
import Submission.Work.DSCOH.Assembly
import Submission.Work.DSMap.Map

namespace Work.DSCOH

theorem comparison_of_cech_model (A : Type*) [CommRing A]
    [HasDerivedCategory (ModuleCat A)] (X : AlgebraicGeometry.Scheme)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [CategoryTheory.EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    {C : CochainComplex (ModuleCat A) ℤ}
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅ DerivedCategory.Q.obj C)
    (K : CochainComplex (ModuleCat A) ℕ)
    (hK : ∀ q : ℕ, Nonempty (C.homology (q : ℤ) ≅ K.homology q)) :
    ∀ q : ℕ, Nonempty ((DerivedCategory.homologyFunctor (ModuleCat A) (q : ℤ)).obj
      (DerivedCategory.Plus.ι.obj (DSMap.RG A X f)) ≅ K.homology q) := by
  intro q
  refine ⟨(DerivedCategory.homologyFunctor (ModuleCat A) (q : ℤ)).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat A) (q : ℤ)).app C ≪≫ (hK q).some⟩

end Work.DSCOH
