import Mathlib
import Submission.Work.DSEQ0.Model
import Submission.Work.DSEQ0.singleZ_isKProjective

namespace Work.DSEQ0

universe u

open scoped CategoryTheory
open CategoryTheory

set_option linter.style.haveILetI false

/-- For a K-projective complex `K`, the localization functor to the derived category is
surjective on morphisms out of `K`: every morphism `Q K ⟶ Q L` in the derived category is the
image of an honest chain map `K ⟶ L`.  This is the form of
`CochainComplex.IsKProjective.Qh_map_bijective` in which we consume it, the homotopy category
and the derived category being identified along `DerivedCategory.quotientCompQhIso`. -/
lemma Q_map_surjective_of_isKProjective {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    {K : CochainComplex (ModuleCat.{u} A) ℤ} [CochainComplex.IsKProjective K]
    (L : CochainComplex (ModuleCat.{u} A) ℤ) :
    Function.Surjective
      (DerivedCategory.Q.map : (K ⟶ L) →
        (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L)) := by
  intro T
  obtain ⟨y, hy⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K _).surjective
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app K ≫ T ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.app L)
  obtain ⟨f, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map_surjective y
  refine ⟨f, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app K),
    ← DerivedCategory.quotientCompQhIso_hom_naturality f, hy]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Lifting a morphism along a quasi-isomorphism: any `cc : A[0] ⟶ K` lifts to a chain map
`c : A[0] ⟶ P` whenever `q : P ⟶ K` is a quasi-isomorphism.  The proof uses that `A[0]` is
K-projective (`CochainComplex.isKProjective_of_projective`, `A[0]` being strictly bounded above
in degree `0` with free terms), so that homotopy classes of chain maps `A[0] ⟶ −` agree with
morphisms in the derived category, together with the fact that `Q q` is an isomorphism.  This is
the step that produces the lift `c` of the Čech coaugmentation in the model data of area `EQ0`;
note that only the *derived* statement is available, not the strict equality `c ≫ q = cc`. -/
theorem exists_lift_of_quasiIso {A : Type u} [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    (P K : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ K) (hq : QuasiIso q)
    (cc : Work.DSEQ0.singleZ A ⟶ K) :
    ∃ c : Work.DSEQ0.singleZ A ⟶ P,
      DerivedCategory.Q.map cc =
        DerivedCategory.Q.map c ≫ DerivedCategory.Q.map q := by
  haveI : QuasiIso q := hq
  haveI : CochainComplex.IsKProjective (Work.DSEQ0.singleZ A) := singleZ_isKProjective
  obtain ⟨c, hc⟩ := Q_map_surjective_of_isKProjective (A := A) P
    (DerivedCategory.Q.map cc ≫ inv (DerivedCategory.Q.map q))
  exact ⟨c, by rw [hc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

end Work.DSEQ0
