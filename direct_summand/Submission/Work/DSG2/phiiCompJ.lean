import Mathlib
import Submission.Work.DSG2.Setup

open CategoryTheory AlgebraicGeometry Limits
universe u
namespace Work.DSG2

theorem phiiCompJ {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)}
    (D : ChowSetup A X f) (i : Fin D.m) :
    ChowSetup.phii D i ≫ D.j i = (ChowSetup.Vi D i).ι ≫ ChowSetup.qi D i := by
  rw [ChowSetup.phii, ← Scheme.Hom.toImage_imageι (D.j i), ← ChowSetup.eUi_hom_ι D i]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc (D.pi i ∣_ D.Wi i) (D.Wi i).ι ((D.j i).imageι),
    morphismRestrict_ι (ChowSetup.pi D i) (ChowSetup.Wi D i), Category.assoc,
    ← ChowSetup.pi_spec D i]

end Work.DSG2
