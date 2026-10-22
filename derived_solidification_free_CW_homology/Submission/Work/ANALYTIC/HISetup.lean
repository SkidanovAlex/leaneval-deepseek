import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.profinite_HI
import Submission.Work.ANALYTIC.PrTop
import Submission.Work.RESOL.exists_atomSkeleton

/-!
# AN6, step 2: the small light-profinite cover `cov Y ⟶ Y` of a topological space

For a topological space `Y` we build a light condensed set `cov Y` together with a map
`covMap Y : cov Y ⟶ Y.toLightCondSet` which is *sectionwise split*: for every light profinite `U`
and every map `t : U ⟶ Y` the map `t` lifts along `covMap Y` on the nose (no cover is needed).

The construction is the one of REFS/04 §3: take a *small* family `skel : skelι → LightProfinite`
of test objects which contains every isomorphism type up to a retract (this is
`Work.RESOL.exists_atomSkeleton`) and let

  `cov Y := ∐_{x = (i, y) : Σ i, Y(skel i)} skel i`

be the coproduct over all pairs (test object, *element* of `Y` over it).  Indexing by elements
(rather than by maps `skel i ⟶ Y`) keeps the index type small, which is what the small coproduct
in `LightCondSet` needs.  Given `t : U ⟶ Y`, choose `i` with `U` a retract of `skel i` through
`e : U ⟶ skel i`, `r : skel i ⟶ U`, `e ≫ r = 𝟙 U`; then the element `t ∘ r ∈ Y(skel i)` is one of
the indices, and `t = e ≫ (t ∘ r)` lifts.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Work.ANALYTIC

/-! ## Small coproducts of light condensed sets

The site `LightProfinite` is essentially small and `Type 0` has all small colimits, so
`LightCondSet` has all *small* coproducts; the instance search for this does not terminate in
reasonable time, so we record the instance (built from the sheafified presheaf coproduct) here and
install it locally where needed. -/

/-- Small coproducts in `LightCondSet`, built as sheafifications of presheaf coproducts. -/
noncomputable def lightCondSetHasCoproduct {ι : Type} (F : ι → LightCondSet.{0}) :
    HasCoproduct F :=
  HasColimit.mk
    ⟨Sheaf.sheafifyCocone (colimit.cocone (Discrete.functor F ⋙ sheafToPresheaf _ (Type 0))),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩

attribute [local instance] lightCondSetHasCoproduct

/-! ## A small skeleton of `LightProfinite` -/

/-- The index type of the skeleton. -/
abbrev skelι : Type := Classical.choose Work.RESOL.exists_atomSkeleton

/-- The small skeleton of `LightProfinite`: every light profinite set is a retract of `skel i` for
some `i`. -/
abbrev skel : skelι → LightProfinite.{0} :=
  Classical.choose (Classical.choose_spec Work.RESOL.exists_atomSkeleton)

/-- Every light profinite set is a retract of a member of the skeleton. -/
theorem skel_retract (X : LightProfinite.{0}) :
    ∃ (i : skelι) (e : X ⟶ skel i) (r : skel i ⟶ X), e ≫ r = 𝟙 X :=
  Classical.choose_spec (Classical.choose_spec Work.RESOL.exists_atomSkeleton) X

/-! ## The cover -/

/-- The index type of the cover of `Y`: a skeleton member together with an element of `Y` over it.
(The type `Y.toLightCondSet.obj.obj (op (skel i))` is the type of continuous maps `skel i ⟶ Y`,
which lives in `Type 0`, so this index type is small.) -/
abbrev CovIdx (Y : TopCat.{0}) : Type :=
  Σ i : skelι, Y.toLightCondSet.obj.obj (Opposite.op (skel i))

/-- The map `skel i ⟶ Y` classified by an index (Yoneda). -/
abbrev covComp (Y : TopCat.{0}) (x : CovIdx Y) :
    lightProfiniteToLightCondSet.{0}.obj (skel x.1) ⟶ Y.toLightCondSet :=
  (coherentTopology LightProfinite.{0}).yonedaEquiv.symm x.2

/-- The cover of `Y`: the coproduct of the skeleton members, indexed by (test object, element). -/
abbrev cov (Y : TopCat.{0}) : LightCondSet.{0} :=
  ∐ (fun x : CovIdx Y => lightProfiniteToLightCondSet.{0}.obj (skel x.1))

/-- The structure map `cov Y ⟶ Y`. -/
abbrev covMap (Y : TopCat.{0}) : cov Y ⟶ Y.toLightCondSet :=
  Sigma.desc (fun x => covComp Y x)

/-- **The cover is sectionwise split.**  For every light profinite `U` and every `t : U ⟶ Y` there
is a lift `s : U ⟶ cov Y` with `s ≫ covMap Y = t`; no refinement of `U` is needed. -/
theorem cov_lift (Y : TopCat.{0}) (U : LightProfinite.{0})
    (t : lightProfiniteToLightCondSet.{0}.obj U ⟶ Y.toLightCondSet) :
    ∃ s : lightProfiniteToLightCondSet.{0}.obj U ⟶ cov Y, s ≫ covMap Y = t := by
  obtain ⟨i, e, r, he⟩ := skel_retract U
  refine ⟨lightProfiniteToLightCondSet.{0}.map e ≫
    Sigma.ι (fun x : CovIdx Y => lightProfiniteToLightCondSet.{0}.obj (skel x.1))
      ⟨i, (coherentTopology LightProfinite.{0}).yonedaEquiv
        (lightProfiniteToLightCondSet.{0}.map r ≫ t)⟩, ?_⟩
  rw [Category.assoc, Sigma.ι_comp_desc]
  show lightProfiniteToLightCondSet.{0}.map e ≫
      (coherentTopology LightProfinite.{0}).yonedaEquiv.symm
        ((coherentTopology LightProfinite.{0}).yonedaEquiv
          (lightProfiniteToLightCondSet.{0}.map r ≫ t)) = t
  rw [Equiv.symm_apply_apply]
  rw [← Category.assoc, ← Functor.map_comp, he]
  simp

/-- A map in `LightCondSet` is locally surjective as soon as it is surjective on sections. -/
theorem isLocallySurjective_of_surjective_sections {A B : LightCondSet.{0}} (f : A ⟶ B)
    (h : ∀ (U : LightProfinite.{0}ᵒᵖ), Function.Surjective (f.hom.app U)) :
    Sheaf.IsLocallySurjective f :=
  (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff f).mpr
    (Presheaf.isLocallySurjective_of_surjective _ f.hom h)

/-- **The cover is surjective on sections.** -/
theorem covMap_surjective_sections (Y : TopCat.{0}) (U : LightProfinite.{0}ᵒᵖ) :
    Function.Surjective ((covMap Y).hom.app U) := by
  intro t
  obtain ⟨s, hs⟩ := cov_lift Y U.unop
    ((coherentTopology LightProfinite.{0}).yonedaEquiv.symm t)
  refine ⟨(coherentTopology LightProfinite.{0}).yonedaEquiv s, ?_⟩
  have h2 : (covMap Y).hom.app U
        ((coherentTopology LightProfinite.{0}).yonedaEquiv s) =
      (coherentTopology LightProfinite.{0}).yonedaEquiv (s ≫ covMap Y) :=
    (GrothendieckTopology.yonedaEquiv_comp (coherentTopology LightProfinite.{0}) s
      (covMap Y)).symm
  rw [h2, hs, Equiv.apply_symm_apply]

/-- **The cover is an epimorphism.** -/
theorem covMap_epi (Y : TopCat.{0}) : Epi (covMap Y) :=
  (Sheaf.isLocallySurjective_iff_epi (covMap Y)).mp
    (isLocallySurjective_of_surjective_sections (covMap Y) (covMap_surjective_sections Y))

end Work.ANALYTIC
