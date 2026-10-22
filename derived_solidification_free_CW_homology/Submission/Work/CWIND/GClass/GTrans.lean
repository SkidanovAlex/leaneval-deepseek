import Mathlib

/-!
# CWIND/GClass — transport of colimit cofans and coproduct isomorphisms

Foundational category-theoretic lemmas for the `sigma` field of the CW induction: how a colimit
cocone over a discrete diagram (i.e. a coproduct) behaves under postcomposition with an
isomorphism and under applying a functor, and that extension of complexes preserves colimits.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' v u

namespace Work.CWIND.GClass

variable {C : Type u} [Category.{v} C] {J : Type w}

/-- If the cofan given by the maps `p j : X j ⟶ Z` is a colimit, then the induced map from the
coproduct is an isomorphism. -/
theorem isIso_sigmaDesc_of_isColimit {X : J → C} {Z : C} (p : ∀ j, X j ⟶ Z)
    [HasCoproduct X] (h : IsColimit (Cofan.mk Z p)) : IsIso (Limits.Sigma.desc p) := by
  refine ⟨⟨h.desc (Cofan.mk (∐ X) (Sigma.ι X)), ?_, ?_⟩⟩
  · apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, Limits.Sigma.ι_comp_desc]
    have hf := IsColimit.fac h (Cofan.mk (∐ X) (Sigma.ι X)) (Discrete.mk j)
    rw [Cofan.mk_ι_app, Cofan.mk_ι_app] at hf
    simpa using hf
  · apply IsColimit.hom_ext h
    intro j
    rcases j with ⟨j⟩
    rw [← Category.assoc, IsColimit.fac]
    simp [Cofan.mk_ι_app]

/-- Conversely, if the induced map from the coproduct is an isomorphism, the cofan is a colimit. -/
def isColimit_cofan_of_isIso {X : J → C} {Z : C} (p : ∀ j, X j ⟶ Z)
    [HasCoproduct X] [IsIso (Limits.Sigma.desc p)] : IsColimit (Cofan.mk Z p) := by
  refine ⟨fun s => inv (Limits.Sigma.desc (f := X) (P := Z) p) ≫
    Limits.Sigma.desc (f := X) (fun j => s.ι.app (Discrete.mk j)), ?_, ?_⟩
  · intro s j
    rcases j with ⟨j⟩
    rw [Cofan.mk_ι_app, ← Limits.Sigma.ι_comp_desc p j]
    simp only [Category.assoc]
    rw [IsIso.hom_inv_id_assoc, Limits.Sigma.ι_comp_desc]
  · intro s m hm
    have hm' : Limits.Sigma.desc p ≫ m =
        Limits.Sigma.desc (f := X) (fun j => s.ι.app (Discrete.mk j)) := by
      apply Sigma.hom_ext
      intro j
      rw [Limits.Sigma.ι_comp_desc_assoc, Limits.Sigma.ι_comp_desc]
      simpa using hm (Discrete.mk j)
    calc m = 𝟙 (Cofan.mk Z p).pt ≫ m := (Category.id_comp m).symm
      _ = (inv (Limits.Sigma.desc (f := X) (P := Z) p) ≫
            Limits.Sigma.desc (f := X) (P := Z) p) ≫ m := by rw [IsIso.inv_hom_id]; simp
      _ = inv (Limits.Sigma.desc (f := X) (P := Z) p) ≫
            (Limits.Sigma.desc (f := X) (P := Z) p ≫ m) := Category.assoc _ _ _
      _ = inv (Limits.Sigma.desc (f := X) (P := Z) p) ≫
            Limits.Sigma.desc (f := X) (fun j => s.ι.app (Discrete.mk j)) := by rw [hm']

/-- A colimit cofan stays a colimit after postcomposition with an isomorphism.  No assumption on
the existence of coproducts is needed: the universal map is obtained from the given colimit. -/
def isColimit_cofan_postcomp_iso {X : J → C} {Z Z' : C} (p : ∀ j, X j ⟶ Z) (e : Z ≅ Z')
    (h : IsColimit (Cofan.mk Z p)) :
    IsColimit (Cofan.mk Z' (fun j => p j ≫ e.hom)) where
  desc s := e.inv ≫ h.desc s
  fac s j := by
    rcases j with ⟨j⟩
    simp only [Cofan.mk_ι_app, Category.assoc]
    rw [Iso.hom_inv_id_assoc]
    simpa using IsColimit.fac h s (Discrete.mk j)
  uniq s m hm := by
    have hkey : e.hom ≫ m = h.desc s :=
      IsColimit.uniq h s (e.hom ≫ m) (fun j => by
        simpa [Cofan.mk_ι_app, Category.assoc] using hm j)
    calc m = 𝟙 Z' ≫ m := (Category.id_comp m).symm
      _ = (e.inv ≫ e.hom) ≫ m := by rw [Iso.inv_hom_id]
      _ = e.inv ≫ (e.hom ≫ m) := Category.assoc _ _ _
      _ = e.inv ≫ h.desc s := by rw [hkey]

/-- Transport of a colimit cofan along a functor that preserves the relevant colimits. -/
def isColimit_cofan_map {D : Type*} [Category.{v} D] {X : J → C} {Z : C}
    (p : ∀ j, X j ⟶ Z) (F : C ⥤ D) [PreservesColimitsOfShape (Discrete J) F]
    (h : IsColimit (Cofan.mk Z p)) :
    IsColimit (Cofan.mk (F.obj Z) (fun j => F.map (p j))) :=
  Cofan.isColimitMapCoconeEquiv F X (Cofan.mk Z p) (isColimitOfPreserves F h)

/-! ## Extension of complexes preserves colimits -/

open ComplexShape in
/-- The extension functor attached to an embedding of complex shapes preserves colimits of any
(small) shape present in the target category. -/
theorem preservesColimitsOfShape_extendFunctor {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasZeroMorphisms C] {ι : Type w} {ι' : Type w} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (J : Type w) [HasColimitsOfShape (Discrete J) C] :
    PreservesColimitsOfShape (Discrete J) (e.extendFunctor C) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i' => ?_)
  rcases h : e.r i' with _ | i
  · have hi' : ∀ i, e.f i ≠ i' := fun i hfi => by
      rw [e.r_eq_some hfi] at h
      exact nomatch h
    exact Functor.preservesColimitsOfShape_of_isZero _
      (Functor.isZero _ (fun K => by
        show IsZero ((K.extend e).X i')
        exact K.isZero_extend_X e i' hi')) _
  · have hfi : e.f i = i' := e.f_eq_of_r_eq_some h
    exact preservesColimitsOfShape_of_natIso (e.extendFunctorCompEvalIso C hfi).symm

end Work.CWIND.GClass
