import Submission.Work.FLAT.Setup

/-!
# AREA FLAT — tensor products with a sheafified object

For a presheaf `F` of abelian groups on light profinite sets, and `X = L(F) = ℤ[·]` its
sheafification, the functor `X ⊗ -` on light condensed abelian groups is computed by

`X ⊗ Z ≅ L(F ⊗ S Z)`

where `S` is the underlying-presheaf functor and `Z ≅ L(S Z)`.  In other words there is an
isomorphism of functors

`tensorLeft (L F) ≅ S ⋙ tensorLeft F ⋙ L`.

Since `S` is a right adjoint (so preserves all limits), `L = sheafification` preserves finite
limits, and `tensorLeft F` is the *sectionwise* tensor product, this reduces flatness of `ℤ[T]`
to the (elementary) flatness of its sectionwise free presheaf.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

namespace Work.FLAT

noncomputable section

/-- `sheafifyCounitNatIso Z : Z ≅ L(S Z)`, the inverse of the counit of the sheafification
adjunction (an isomorphism because `S` is fully faithful). -/
noncomputable abbrev sheafifyCounitNatIso : 𝟭 LightCondAb ≅ presheafOf ⋙ sheafify :=
  (asIso (sheafificationAdjunction siteJ (ModuleCat.{0} ℤ)).counit).symm

lemma sheafifyCounitIso_eq (Z : LightCondAb) :
    sheafifyCounitIso Z = sheafifyCounitNatIso.app Z := rfl

/-- The identification `L F ⊗ Z ≅ L(F ⊗ S Z)`, natural in the light condensed abelian group `Z`:
tensoring with a sheafified object is the sheafification of the sectionwise tensor product. -/
noncomputable def tensorLeftSheafifyIso (F : PreMod) :
    tensorLeft (sheafify.obj F) ≅ presheafOf ⋙ tensorLeft F ⋙ sheafify :=
  NatIso.ofComponents
    (fun Z => tensorIso (Iso.refl (sheafify.obj F)) (sheafifyCounitNatIso.app Z) ≪≫
      Functor.Monoidal.μIso sheafify F (presheafOf.obj Z))
    (by
      intro Z Z' h
      dsimp only [Functor.comp_obj, Functor.comp_map]
      simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Functor.Monoidal.μIso_hom]
      have hnat : h ≫ (sheafifyCounitNatIso.app Z').hom =
          (sheafifyCounitNatIso.app Z).hom ≫ sheafify.map (presheafOf.map h) :=
        sheafifyCounitNatIso.hom.naturality h
      rw [show (tensorLeft (sheafify.obj F)).map h = sheafify.obj F ◁ h from rfl,
        show (tensorLeft F).map (presheafOf.map h) = F ◁ presheafOf.map h from rfl]
      simp only [id_tensorHom]
      rw [← whiskerLeft_comp_assoc, hnat, whiskerLeft_comp_assoc,
        Functor.LaxMonoidal.μ_natural_right]
      simp [Category.assoc])

/-- If the sectionwise tensor product with `F` preserves finite limits, so does the tensor
product with the sheafified object `L F`. -/
lemma preservesFiniteLimits_tensorLeft_sheafify (F : PreMod) [PreservesFiniteLimits (tensorLeft F)] :
    PreservesFiniteLimits (tensorLeft (sheafify.obj F)) :=
  preservesFiniteLimits_of_natIso (tensorLeftSheafifyIso F).symm

end

end Work.FLAT
