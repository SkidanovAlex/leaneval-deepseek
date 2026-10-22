import Mathlib
import Submission.Work.REFL.Basic

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed Opposite

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.REFL

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The coherent topology on `LightProfinite.{0}`. -/
abbrev pcisTop : GrothendieckTopology LightProfinite.{0} := coherentTopology LightProfinite.{0}

/-- The coefficient category: `ℤ`-modules. -/
abbrev pcisMod := ModuleCat.{0} ℤ

/-- The underlying-presheaf functor on light condensed abelian groups. -/
abbrev pcisSh : LightCondAb ⥤ (LightProfinite.{0}ᵒᵖ ⥤ pcisMod) := sheafToPresheaf pcisTop pcisMod

section Main

variable {K : Type} [SmallCategory K] [IsFiltered K]

/-- The point of the pointwise colimit cocone of a filtered diagram of presheaves of abelian
groups (each degreewise a filtered colimit) preserves finite products. -/
theorem pointwiseCocone_preservesFiniteProducts (H : K ⥤ (LightProfinite.{0}ᵒᵖ ⥤ pcisMod))
    (hH : ∀ k, PreservesFiniteProducts (H.obj k)) :
    PreservesFiniteProducts ((pointwiseCocone H).pt) := by
  rw [pointwiseCocone_pt]
  have h1 : PreservesFiniteProducts H.flip := by
    refine ⟨fun n => Limits.preservesLimitsOfShape_of_evaluation _ _ (fun k => ?_)⟩
    exact (hH k).preserves n
  letI := h1
  exact Limits.comp_preservesFiniteProducts H.flip colim

/-- The action of `colimMap` on representatives of a filtered colimit. -/
theorem colimMap_ι_apply {A B : K ⥤ pcisMod} (α : A ⟶ B) (j : K) (x : ToType (A.obj j)) :
    (colimMap α) ((colimit.ι A j) x) = (colimit.ι B j) (α.app j x) := by
  have h := ConcreteCategory.congr_hom (ι_colimMap α j) x
  simpa only [ConcreteCategory.comp_apply] using h

/-- The `colimit.ι` of a filtered colimit are compatible with the connecting maps. -/
theorem colimit_ι_map_apply {A : K ⥤ pcisMod} {i k : K} (u : i ⟶ k) (x : ToType (A.obj i)) :
    (colimit.ι A k) ((A.map u) x) = (colimit.ι A i) x := by
  have h := ConcreteCategory.congr_hom (colimit.w A u) x
  simpa only [ConcreteCategory.comp_apply] using h

/-- The point of the pointwise colimit cocone of a filtered diagram of sheaves of types on
`LightProfinite` satisfies the equalizer condition (for the coherent topology). -/
theorem pointwiseCocone_equalizerCondition (H : K ⥤ (LightProfinite.{0}ᵒᵖ ⥤ pcisMod))
    (hH : ∀ k, Presheaf.IsSheaf pcisTop (H.obj k)) :
    regularTopology.EqualizerCondition ((pointwiseCocone H).pt ⋙ forget pcisMod) := by
  have hstage : ∀ k, regularTopology.EqualizerCondition ((H.obj k) ⋙ forget pcisMod) := fun k =>
    ((Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
        ((H.obj k) ⋙ forget pcisMod)).mp
      (Presheaf.isSheaf_comp_of_isSheaf pcisTop (H.obj k) (forget pcisMod) (hH k))).2
  refine regularTopology.EqualizerCondition.mk' _ (fun X B π _ c0 hc0 => ?_)
  let Q : LightProfinite.{0}ᵒᵖ ⥤ pcisMod := (pointwiseCocone H).pt
  have hbij : ∀ k, Function.Bijective
      (regularTopology.mapToEqualizer ((H.obj k) ⋙ forget pcisMod) π c0.fst c0.snd c0.condition) :=
    fun k => (hstage k).bijective_mapToEqualizer_pullback' (π := π) c0 hc0
  refine ⟨?_, ?_⟩
  · -- injectivity
    intro y y' hyy
    have hyy' : (Q.map π.op) y = (Q.map π.op) y' := by
      have h := congrArg Subtype.val hyy
      simp only [regularTopology.mapToEqualizer] at h
      simpa using h
    obtain ⟨i, yi, hyi⟩ := Concrete.colimit_exists_rep (H.flip.obj (op B)) y
    obtain ⟨j, yj, hyj⟩ := Concrete.colimit_exists_rep (H.flip.obj (op B)) y'
    rw [← hyi, ← hyj] at hyy'
    have h2 : (colimMap (H.flip.map π.op)) ((colimit.ι (H.flip.obj (op B)) i) yi) =
        (colimMap (H.flip.map π.op)) ((colimit.ι (H.flip.obj (op B)) j) yj) := hyy'
    have h3 : (colimit.ι (H.flip.obj (op X)) i) ((H.flip.map π.op).app i yi) =
        (colimit.ι (H.flip.obj (op X)) j) ((H.flip.map π.op).app j yj) :=
      (colimMap_ι_apply (H.flip.map π.op) i yi).symm.trans
        (h2.trans (colimMap_ι_apply (H.flip.map π.op) j yj))
    obtain ⟨k, f, g, hfg⟩ :=
      (IsColimit.eq_iff (H.flip.obj (op X)) (colimit.isColimit (H.flip.obj (op X)))).mp h3
    have h4 : (H.flip.map π.op).app k ((H.flip.obj (op B)).map f yi) =
        (H.flip.map π.op).app k ((H.flip.obj (op B)).map g yj) := by
      rw [NatTrans.naturality_apply (H.flip.map π.op) f yi,
        NatTrans.naturality_apply (H.flip.map π.op) g yj]
      exact hfg
    have hkinj : Function.Injective
        (fun b : ToType ((H.obj k).obj (op B)) => ((H.obj k).map π.op) b) := by
      intro a b hab
      refine (hbij k).1 (Subtype.ext ?_)
      simp only [regularTopology.mapToEqualizer]
      simpa using hab
    have h5 : (H.flip.obj (op B)).map f yi = (H.flip.obj (op B)).map g yj :=
      hkinj (by simpa only [Functor.flip_map_app] using h4)
    have h6 : (colimit.ι (H.flip.obj (op B)) i) yi = (colimit.ι (H.flip.obj (op B)) j) yj :=
      Concrete.isColimit_rep_eq_of_exists (H.flip.obj (op B)) yi yj ⟨k, f, g, h5⟩
    rw [← hyi, ← hyj]
    exact h6
  · -- surjectivity
    rintro ⟨y, hy⟩
    have hyy : (Q.map c0.fst.op) y = (Q.map c0.snd.op) y := by
      simpa using hy
    obtain ⟨i, yi, hyi⟩ := Concrete.colimit_exists_rep (H.flip.obj (op X)) y
    rw [← hyi] at hyy
    have h2 : (colimMap (H.flip.map c0.fst.op)) ((colimit.ι (H.flip.obj (op X)) i) yi) =
        (colimMap (H.flip.map c0.snd.op)) ((colimit.ι (H.flip.obj (op X)) i) yi) := hyy
    have h3 : (colimit.ι (H.flip.obj (op c0.pt)) i) ((H.flip.map c0.fst.op).app i yi) =
        (colimit.ι (H.flip.obj (op c0.pt)) i) ((H.flip.map c0.snd.op).app i yi) :=
      (colimMap_ι_apply (H.flip.map c0.fst.op) i yi).symm.trans
        (h2.trans (colimMap_ι_apply (H.flip.map c0.snd.op) i yi))
    obtain ⟨k, u, hu⟩ := (IsColimit.eq_iff'
      (colimit.isColimit (H.flip.obj (op c0.pt)))
      ((H.flip.map c0.fst.op).app i yi) ((H.flip.map c0.snd.op).app i yi)).mp h3
    have h4 : (H.flip.map c0.fst.op).app k ((H.flip.obj (op X)).map u yi) =
        (H.flip.map c0.snd.op).app k ((H.flip.obj (op X)).map u yi) := by
      rw [NatTrans.naturality_apply (H.flip.map c0.fst.op) u yi,
        NatTrans.naturality_apply (H.flip.map c0.snd.op) u yi]
      exact hu
    have h4' : (H.obj k).map c0.fst.op ((H.flip.obj (op X)).map u yi) =
        (H.obj k).map c0.snd.op ((H.flip.obj (op X)).map u yi) := by
      simpa only [Functor.flip_map_app] using h4
    have hmem : ((H.obj k) ⋙ forget pcisMod).map c0.fst.op ((H.flip.obj (op X)).map u yi) =
        ((H.obj k) ⋙ forget pcisMod).map c0.snd.op ((H.flip.obj (op X)).map u yi) := h4'
    obtain ⟨b, hb⟩ := (hbij k).2 ⟨(H.flip.obj (op X)).map u yi, hmem⟩
    have hb' : ((H.obj k).map π.op) b = (H.flip.obj (op X)).map u yi := by
      have h := congrArg Subtype.val hb
      simp only [regularTopology.mapToEqualizer] at h
      simpa using h
    refine ⟨(colimit.ι (H.flip.obj (op B)) k) b, ?_⟩
    refine Subtype.ext ?_
    simp only [regularTopology.mapToEqualizer, Functor.comp_map,
      ConcreteCategory.hom_ofHom]
    have key : (colimMap (H.flip.map π.op)) ((colimit.ι (H.flip.obj (op B)) k) b) = y :=
      (colimMap_ι_apply (H.flip.map π.op) k b).trans <| by
        rw [Functor.flip_map_app, hb']
        exact (colimit_ι_map_apply u yi).trans hyi
    exact key

/-- Filtered colimits of light condensed abelian groups are computed pointwise. -/
theorem isSheaf_pointwiseCocone (H : K ⥤ (LightProfinite.{0}ᵒᵖ ⥤ pcisMod))
    (hH : ∀ k, Presheaf.IsSheaf pcisTop (H.obj k)) :
    Presheaf.IsSheaf pcisTop ((pointwiseCocone H).pt) := by
  have hprod : ∀ k, PreservesFiniteProducts (H.obj k) := fun k =>
    ((Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition (H.obj k)).mp
      (hH k)).1
  letI := pointwiseCocone_preservesFiniteProducts H hprod
  refine Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp _ (forget pcisMod) ?_
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
  exact ⟨inferInstance, pointwiseCocone_equalizerCondition H hH⟩

end Main


/-- **Filtered colimits of light condensed abelian groups are computed pointwise.** -/
theorem pointwise_colimit_isSheaf : Work.REFL.PointwiseColimitIsSheaf := by
  intro K _ _ F c hc
  have hsh : Presheaf.IsSheaf pcisTop ((pointwiseCocone (F ⋙ pcisSh)).pt) :=
    isSheaf_pointwiseCocone (F ⋙ pcisSh) (fun k => (F.obj k).property)
  exact (Presheaf.isSheaf_of_iso_iff
    (IsColimit.coconePointUniqueUpToIso hc (pointwiseIsColimit (F ⋙ pcisSh)))).mpr hsh

end Work.REFL
