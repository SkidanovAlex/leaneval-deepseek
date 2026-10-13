import Mathlib

namespace Work.DSG4a.chainSplitBC

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
universe u

theorem quotient_map_eq_of_Q_map_eq_comp {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    (S : CochainComplex (ModuleCat.{u} A) ℤ) [S.IsKProjective]
    {P C : CochainComplex (ModuleCat.{u} A) ℤ} (cc : S ⟶ P) (q : P ⟶ C) (ccAn : S ⟶ C)
    (h : DerivedCategory.Q.map ccAn = DerivedCategory.Q.map cc ≫ DerivedCategory.Q.map q) :
    (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map (cc ≫ q) =
      (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map ccAn := by
  have h' : DerivedCategory.Q.map (cc ≫ q) = DerivedCategory.Q.map ccAn := by
    rw [h, Functor.map_comp]
  refine (CochainComplex.IsKProjective.Qh_map_bijective (C := ModuleCat.{u} A) S
    ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj C)).injective ?_
  have h1 := DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{u} A) (cc ≫ q)
  have h2 := DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{u} A) ccAn
  rw [h'] at h1
  exact (cancel_mono ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app C)).mp
    (h1.trans h2.symm)

end Work.DSG4a.chainSplitBC
