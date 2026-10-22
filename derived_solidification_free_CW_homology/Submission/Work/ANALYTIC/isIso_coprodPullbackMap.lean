import Mathlib
import Submission.Work.ANALYTIC.CechPt.cech_descent
import Submission.Work.ANALYTIC.isUniversalColimit_colimitCocone_lightCondSet

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The canonical comparison map from the coproduct of the pullbacks to the pullback of the
coproduct. -/
noncomputable def coprodPullbackMap {ι : Type} {F : ι → LightCondSet.{0}} [HasCoproduct F]
    {Z W : LightCondSet.{0}} (φ : ∀ x, F x ⟶ Z) (ψ : W ⟶ Z)
    [HasCoproduct (fun x => pullback (φ x) ψ)] :
    (∐ (fun x => pullback (φ x) ψ)) ⟶ pullback (Sigma.desc φ) ψ :=
  Sigma.desc (fun x => pullback.lift (pullback.fst (φ x) ψ ≫ Sigma.ι F x)
    (pullback.snd (φ x) ψ) (by
      rw [Category.assoc, Sigma.ι_comp_desc]
      exact pullback.condition))

/-- The `x`-th coproduct inclusion followed by `coprodPullbackMap` is the canonical map from
`F x ×_Z W` to `(∐ F) ×_Z W`. -/
lemma Sigma_ι_comp_coprodPullbackMap {ι : Type} {F : ι → LightCondSet.{0}} [HasCoproduct F]
    {Z W : LightCondSet.{0}} (φ : ∀ x, F x ⟶ Z) (ψ : W ⟶ Z)
    [HasCoproduct (fun x => pullback (φ x) ψ)] (x : ι) :
    Sigma.ι (fun x => pullback (φ x) ψ) x ≫ coprodPullbackMap φ ψ =
      pullback.lift (pullback.fst (φ x) ψ ≫ Sigma.ι F x)
        (pullback.snd (φ x) ψ) (by
          rw [Category.assoc, Sigma.ι_comp_desc]
          exact pullback.condition) := by
  rw [coprodPullbackMap, Sigma.ι_comp_desc]

/-- `Sigma.desc` agrees with `Cofan.IsColimit.desc` for the canonical coproduct cofan. -/
lemma sigma_desc_eq_cofan_desc {β : Type} {D : Type*} [Category* D] {f : β → D} [HasCoproduct f]
    {A : D} (g : (b : β) → f b ⟶ A) :
    Sigma.desc g = Cofan.IsColimit.desc (coproductIsCoproduct f) g := by
  refine Cofan.IsColimit.hom_ext (coproductIsCoproduct f) _ _ (fun b => ?_)
  rw [Cofan.IsColimit.fac (coproductIsCoproduct f) g b]
  simp only [Cofan.inj, Cofan.mk_ι_app, Sigma.ι_comp_desc]

/-- If a coproduct cocone in `LightCondSet` is universal then pulling it back along any map
decomposes it as the coproduct of the pullbacks. -/
private lemma isIso_coprodPullbackMap_of_universal {ι : Type} {F : ι → LightCondSet.{0}}
    [HasCoproduct F] {Z W : LightCondSet.{0}} (φ : ∀ x, F x ⟶ Z) (ψ : W ⟶ Z)
    [HasCoproduct (fun x => pullback (φ x) ψ)]
    (hau : IsUniversalColimit (Cofan.mk (∐ F) (Sigma.ι F))) :
    IsIso (coprodPullbackMap φ ψ) := by
  have hpb : IsPullback
      (Cofan.IsColimit.desc (coproductIsCoproduct (fun x => pullback (φ x) ψ))
        (fun x => pullback.fst (φ x) ψ ≫ Sigma.ι F x))
      (Cofan.IsColimit.desc (coproductIsCoproduct (fun x => pullback (φ x) ψ))
        (fun x => pullback.snd (φ x) ψ))
      (Sigma.desc φ) ψ :=
    IsUniversalColimit.isPullback_of_isColimit_right hau φ (Sigma.desc φ) ψ
      (fun x => pullback.fst (φ x) ψ) (fun x => pullback.snd (φ x) ψ)
      (fun x => IsPullback.of_hasPullback _ _)
      (coproductIsCoproduct (fun x => pullback (φ x) ψ))
      (fun x => Sigma.ι_comp_desc φ x)
  have key : coprodPullbackMap φ ψ = hpb.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [IsPullback.isoPullback_hom_fst]
      rw [← sigma_desc_eq_cofan_desc (fun x => pullback.fst (φ x) ψ ≫ Sigma.ι F x)]
      refine Sigma.hom_ext _ _ (fun x => ?_)
      rw [← Category.assoc, Sigma_ι_comp_coprodPullbackMap, pullback.lift_fst,
        Sigma.ι_comp_desc]
    · rw [IsPullback.isoPullback_hom_snd]
      rw [← sigma_desc_eq_cofan_desc (fun x => pullback.snd (φ x) ψ)]
      refine Sigma.hom_ext _ _ (fun x => ?_)
      rw [← Category.assoc, Sigma_ι_comp_coprodPullbackMap, pullback.lift_snd,
        Sigma.ι_comp_desc]
  rw [key]
  exact hpb.isoPullback.isIso_hom

/-- Universality of the canonical coproduct cocone of a family follows from universality of the
canonical colimit cocone. -/
private lemma isUniversalColimit_cofan_of_colimitCocone {ι : Type} {F : ι → LightCondSet.{0}}
    [HasCoproduct F]
    (h : IsUniversalColimit (colimit.cocone (Discrete.functor F))) :
    IsUniversalColimit (Cofan.mk (∐ F) (Sigma.ι F)) := by
  refine IsUniversalColimit.of_iso h (Cocone.ext ?_ ?_)
  · exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor F))
      (coproductIsCoproduct F)
  · intro j
    exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j

/-- **Small coproducts in `LightCondSet` are universal.**  Pulling back a small coproduct of light
condensed sets along a map decomposes it as the coproduct of the pullbacks of the summands; i.e.
the canonical map `∐_x (F x ×_Z W) ⟶ (∐_x F x) ×_Z W` is an isomorphism. -/
theorem isIso_coprodPullbackMap {ι : Type} {F : ι → LightCondSet.{0}} [HasCoproduct F]
    {Z W : LightCondSet.{0}} (φ : ∀ x, F x ⟶ Z) (ψ : W ⟶ Z)
    [HasCoproduct (fun x => pullback (φ x) ψ)] :
    IsIso (coprodPullbackMap φ ψ) := by
  refine isIso_coprodPullbackMap_of_universal φ ψ ?_
  exact isUniversalColimit_cofan_of_colimitCocone
    (isUniversalColimit_colimitCocone_lightCondSet (F := Discrete.functor F))

end Work.ANALYTIC
