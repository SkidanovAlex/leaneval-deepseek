import Mathlib
import Submission.Work.DSG4a.BaseChange
import Submission.Work.DSG1.Basic

/-! The universe `u` of the statement (as in the sibling files of the area). -/
universe u

namespace Work.DSG4a

theorem phiU_comp {A : Type u} [CommRing A] {X X' : AlgebraicGeometry.Scheme.{u}}
    (g : X' ⟶ X) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) (U : X.Opens) (a : A) :
    ((AlgebraicGeometry.Scheme.Hom.app g U).hom) (DSMap.phiU A X f U a) =
      DSMap.phiU A X' (Work.DSG4a.compToSpec g f) (Work.DSG4a.preimageOpen g U) a := by
  -- The structure map of `g ≫ f` is the structure map of `f` followed by restriction
  -- along `g` (`Work.DSG1.phi_comp`, i.e. naturality of the `Γ ⊣ Spec` adjunction).
  have hphi : (AlgebraicGeometry.Scheme.Hom.appTop g).hom (DSMap.phi A X f a)
      = DSMap.phi A X' (CategoryTheory.CategoryStruct.comp g f) a := by
    have h := DFunLike.congr_fun (Work.DSG1.phi_comp (A := A) f g).symm a
    simpa [Work.DSG1.gammaMap] using h
  -- Unfold `phiU` into "restrict to `U` after `phi`".
  simp only [DSMap.phiU, RingHom.coe_comp, Function.comp_apply]
  -- `compToSpec g f` is `g ≫ f` by definition.
  rw [show DSMap.phi A X' (CategoryTheory.CategoryStruct.comp g f)
      = DSMap.phi A X' (Work.DSG4a.compToSpec g f) from rfl]
  rw [← hphi]
  -- Naturality of the restriction map of `g`: restricting to `U` and then pulling back
  -- along `g` is the same as pulling back to the global sections and then restricting.
  have sq := AlgebraicGeometry.Scheme.Hom.naturality (f := g) (U := U) (U' := ⊤)
    (i := (CategoryTheory.homOfLE le_top).op)
  have key := congrArg (fun φ => CommRingCat.Hom.hom φ (DSMap.phi A X f a)) sq
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
  exact key

end Work.DSG4a
