import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.CechSheafRestr
import Submission.Work.DSF1.Cech.CechComponents
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi

/-!
# Transport of Čech triviality from the restriction `restrP P V` to `P`

Main result: `Work.DSF1.Sheaf.cechTrivAll_of_restrP`.

Let `U : ι → X.Opens` be a family of opens with `iSup U = V` and let `P` be a presheaf of
abelian groups on `X`.  Then every open of the form `⋂_a U (x a)` (the value of the Čech nerve
of `U` at a simplex `x`) is contained in `V`, and consequently the component of the comparison
map `P ⟶ restrP P V` at such an open is an isomorphism.  Since Mathlib's Čech complex only
evaluates a presheaf at those opens, the induced cochain map

`Č(U, P) ⟶ Č(U, restrP P V)`

is a degreewise isomorphism, hence an isomorphism of complexes; triviality of the Čech
cohomology is transported along it.

The file contains the small general lemmas used for this:

* `isIso_homOfLE_of_eq`: a `homOfLE` morphism between equal objects of a preorder (category) is
  an isomorphism;
* `isIso_pi_of_π`: a morphism of products `∏ᶜ f ⟶ ∏ᶜ g` is an isomorphism as soon as it is the
  product of isomorphisms `f b ≅ g b` (detected on the components `φ ≫ π`);
* `cechTrivAll_of_iso`: `CechTrivAll` is invariant under isomorphisms of cochain complexes.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The canonical natural transformation `P ⟶ restrP P V`, given on an open `W` by the
restriction `P W ⟶ P (W ⊓ V)`. -/
noncomputable def restrPHom (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (V : X.Opens) :
    P ⟶ restrP P V where
  app W := P.map (homOfLE (inf_le_left : W.unop ⊓ V ≤ W.unop)).op
  naturality {W W'} f := by
    have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    rw [hf, restrP_map_homOfLE]
    rw [← P.map_comp, ← P.map_comp]
    exact congrArg (fun m => P.map m) (Subsingleton.elim _ _)

/-- A `homOfLE` morphism between equal objects of a preorder is an isomorphism. -/
lemma isIso_homOfLE_of_eq {α : Type*} [Preorder α] {x y : α} (h : x ≤ y) (hxy : x = y) :
    IsIso (homOfLE h) := by
  subst hxy
  rw [Subsingleton.elim (homOfLE h) (𝟙 x)]
  infer_instance

/-- A morphism `∏ᶜ f ⟶ ∏ᶜ g` which is componentwise given by an isomorphism `f b ≅ g b` is an
isomorphism. -/
lemma isIso_pi_of_π {C : Type*} [Category C] {β : Type*} {f g : β → C}
    [HasProduct f] [HasProduct g]
    (φ : ∏ᶜ f ⟶ ∏ᶜ g) (e : ∀ b, f b ≅ g b)
    (h : ∀ b, φ ≫ Pi.π g b = Pi.π f b ≫ (e b).hom) : IsIso φ := by
  refine IsIso.mk ⟨Pi.lift (fun b => Pi.π g b ≫ (e b).inv), ?_, ?_⟩
  · refine Pi.hom_ext _ _ (fun b => ?_)
    rw [Category.assoc, Pi.lift_comp_π, ← Category.assoc, h b, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · refine Pi.hom_ext _ _ (fun b => ?_)
    rw [Category.assoc, h b, ← Category.assoc, Pi.lift_comp_π, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- Every open of the Čech nerve of `U` is contained in `V` if `iSup U = V`: indeed it is an
intersection of members of the family. -/
lemma cech_obj_le_of_iSup_eq {ι : Type u} (U : ι → X.Opens) (V : X.Opens) (hV : iSup U = V)
    (n : ℕ) (y : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I) :
    ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y ≤ V :=
  (leOfHom (Pi.π (fun a : Fin (n + 1) => U (y a)) 0)).trans
    ((le_iSup U (y 0)).trans (le_of_eq hV))

/-- The comparison map `Č(U, P) ⟶ Č(U, restrP P V)` is an isomorphism of cochain complexes
whenever `iSup U = V`. -/
lemma isIso_cechComplexFunctor_map_restrPHom {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (V : X.Opens) (hV : iSup U = V) :
    IsIso ((cechComplexFunctor U).map (restrPHom P V)) := by
  haveI : ∀ n : ℕ, IsIso (((cechComplexFunctor U).map (restrPHom P V)).f n) := by
    intro n
    refine isIso_pi_of_π (φ := ((cechComplexFunctor U).map (restrPHom P V)).f n)
      (f := fun y : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I =>
        P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
      (g := fun y : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I =>
        (restrP P V).obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
      (e := fun y => ?_) (h := fun y => ?_)
    · haveI : IsIso (homOfLE (inf_le_left :
          ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y ⊓ V ≤
            ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)) :=
        isIso_homOfLE_of_eq _ (inf_eq_left.mpr (cech_obj_le_of_iSup_eq U V hV n y))
      exact asIso (P.map (homOfLE (inf_le_left :
        ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y ⊓ V ≤
          ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)).op)
    · rw [Cech.cechComplexFunctor_map_pi]
      rfl
  exact HomologicalComplex.Hom.isIso_of_components _

/-- `CechTrivAll` is invariant under isomorphism of cochain complexes of abelian groups. -/
lemma cechTrivAll_of_iso {K₁ K₂ : CochainComplex AddCommGrpCat.{u} ℕ} (e : K₂ ≅ K₁)
    (h : CechTrivAll K₁) : CechTrivAll K₂ := by
  intro p x hx
  have hcyc : K₁.d (p + 1) (p + 2) (e.hom.f (p + 1) x) = 0 := by
    have hcomm := HomologicalComplex.Hom.comm e.hom (p + 1) (p + 2)
    have h2 := congrArg (fun (g : K₂.X (p + 1) ⟶ K₁.X (p + 2)) => g x) hcomm
    simpa only [AddCommGrpCat.comp_apply, hx, map_zero] using h2
  obtain ⟨y, hy⟩ := h p _ hcyc
  refine ⟨e.inv.f p y, ?_⟩
  have hcomm := HomologicalComplex.Hom.comm e.inv p (p + 1)
  have h2 := congrArg (fun (g : K₁.X p ⟶ K₂.X (p + 1)) => g y) hcomm
  simp only [AddCommGrpCat.comp_apply] at h2
  rw [h2, hy]
  have h3 : e.hom.f (p + 1) ≫ e.inv.f (p + 1) = 𝟙 (K₂.X (p + 1)) := by
    rw [← HomologicalComplex.comp_f, e.hom_inv_id]
    rfl
  have h4 := congrArg (fun (g : K₂.X (p + 1) ⟶ K₂.X (p + 1)) => g x) h3
  simpa only [AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply] using h4

theorem cechTrivAll_of_restrP {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (V : X.Opens) (hV : iSup U = V)
    (h : Work.DSF1.Sheaf.CechTrivAll
      ((CategoryTheory.cechComplexFunctor U).obj (Work.DSF1.Sheaf.restrP P V))) :
    Work.DSF1.Sheaf.CechTrivAll ((CategoryTheory.cechComplexFunctor U).obj P) := by
  haveI : IsIso ((cechComplexFunctor U).map (restrPHom P V)) :=
    isIso_cechComplexFunctor_map_restrPHom U P V hV
  exact cechTrivAll_of_iso (asIso ((cechComplexFunctor U).map (restrPHom P V))) h

end Work.DSF1.Sheaf
