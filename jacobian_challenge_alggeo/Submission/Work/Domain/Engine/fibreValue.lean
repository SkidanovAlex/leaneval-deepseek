import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.Domain.Engine

variable {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
  [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
  [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]

set_option backward.isDefEq.respectTransparency false in
/-- The point `pr₁ (toGraph η)` of `X` (where `η` is the point of the domain of `g` over the
generic point of `X`) is the generic point of `X`. -/
lemma fv_pr₁_eta (g : X.PartialMap Y) [hg : g.IsOver S] :
    PartialMap.pr₁ S g (PartialMap.toGraph S g (PartialMap.etaDomain g)) = genericPoint X := by
  have h2 := congrArg (fun (f : g.domain.toScheme ⟶ X) => f (PartialMap.etaDomain g))
    (PartialMap.toGraph_pr₁ S g)
  change PartialMap.pr₁ S g (PartialMap.toGraph S g (PartialMap.etaDomain g)) = genericPoint X at h2
  simpa only [PartialMap.etaDomain_eq g] using h2

/-- Transporting a restriction map along an inseparable point. -/
lemma fv_stalkSpecializes_stalkCongr {Z : Scheme} [IrreducibleSpace Z] {a b : Z}
    (h : a ⤳ b) (e : Inseparable a (genericPoint Z)) :
    Z.presheaf.stalkSpecializes h ≫ (Z.presheaf.stalkCongr e).hom =
      Z.presheaf.stalkSpecializes ((genericPoint_spec Z).specializes trivial) := by
  have h1 : (Z.presheaf.stalkCongr e).hom = Z.presheaf.stalkSpecializes e.ge := rfl
  rw [h1, TopCat.Presheaf.stalkSpecializes_comp (F := Z.presheaf) (x := genericPoint Z)
    (y := a) (z := b) e.ge h]

set_option backward.isDefEq.respectTransparency false in
/-- `toGraph.stalkMap η` followed by the germ map of `g` is the transport map from the stalk of
`X` at `pr₁ (toGraph η)` to `K(X)`. -/
lemma fv_crux (g : X.PartialMap Y) [hg : g.IsOver S] (γ : PartialMap.graph S g) :
    (PartialMap.pr₁ S g).stalkMap (PartialMap.toGraph S g (PartialMap.etaDomain g))
      ≫ (Scheme.Hom.stalkMap (PartialMap.toGraph S g) (PartialMap.etaDomain g)
         ≫ (g.domain.stalkIso (PartialMap.etaDomain g)).hom)
    = (X.presheaf.stalkCongr (Inseparable.of_eq (fv_pr₁_eta g))).hom := by
  rw [← Category.assoc, ← Scheme.Hom.stalkMap_comp (PartialMap.toGraph S g) (PartialMap.pr₁ S g)
    (PartialMap.etaDomain g)]
  rw [Scheme.Hom.stalkMap_congr_hom (PartialMap.toGraph S g ≫ PartialMap.pr₁ S g) (g.domain.ι)
    (PartialMap.toGraph_pr₁ S g) (PartialMap.etaDomain g)]
  rw [Category.assoc, ← Scheme.Opens.stalkIso_inv (g.domain) (PartialMap.etaDomain g),
    Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- `θ_γ` is a retraction of the stalk map of `pr₁`. -/
lemma fv_theta_comp_stalkMap (g : X.PartialMap Y) [hg : g.IsOver S] (γ : PartialMap.graph S g) :
    (PartialMap.pr₁ S g).stalkMap γ ≫ PartialMap.theta g γ =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk ((PartialMap.pr₁ S g) γ)) X.functionField) := by
  rw [PartialMap.theta, PartialMap.germMapToFunctionField]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc (PartialMap.pr₁ S g)]
  rw [fv_crux g γ]
  rw [fv_stalkSpecializes_stalkCongr
      ((PartialMap.pr₁ S g).base.hom.map_specializes (PartialMap.specializes_toGraph_etaDomain g γ))
      (Inseparable.of_eq (fv_pr₁_eta g))]
  rfl

/-- Pointwise form of `fv_theta_comp_stalkMap`. -/
lemma fv_theta_stalkMap_apply (g : X.PartialMap Y) [hg : g.IsOver S] (γ : PartialMap.graph S g)
    (s : X.presheaf.stalk (PartialMap.pr₁ S g γ)) :
    algebraMap (X.presheaf.stalk (PartialMap.pr₁ S g γ)) X.functionField s
      = (PartialMap.theta g γ).hom (((PartialMap.pr₁ S g).stalkMap γ).hom s) := by
  have h3 := DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (fv_theta_comp_stalkMap (S := S) g γ)) s
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
  exact h3.symm

set_option backward.isDefEq.respectTransparency false in
/-- The germ map of the open domain of `g` is the inverse of the stalk map of the inclusion. -/
lemma fv_stalkIso_hom_eq_inv (g : X.PartialMap Y) [hg : g.IsOver S] :
    (g.domain.stalkIso (PartialMap.etaDomain g)).hom
      = inv (Scheme.Hom.stalkMap (g.domain.ι) (PartialMap.etaDomain g)) := by
  have hI : IsIso (Scheme.Hom.stalkMap (g.domain.ι) (PartialMap.etaDomain g)) := by
    rw [← Scheme.Opens.stalkIso_inv (g.domain) (PartialMap.etaDomain g)]
    exact Iso.isIso_inv _
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← Scheme.Opens.stalkIso_inv (g.domain) (PartialMap.etaDomain g), Iso.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
/-- `Spec.map θ_γ` followed by the restriction of `pr₂` to the generic point of `Γ` is the value
of `g` at the generic point of `X`. -/
lemma fv_theta_fromSpecStalk (g : X.PartialMap Y) [hg : g.IsOver S] (γ : PartialMap.graph S g) :
    Spec.map (PartialMap.theta g γ) ≫ (PartialMap.graph S g).fromSpecStalk γ ≫ PartialMap.pr₂ S g
      = g.fromFunctionField := by
  rw [PartialMap.theta, PartialMap.germMapToFunctionField]
  rw [Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc,
    Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, PartialMap.toGraph_pr₂ S g]
  rw [← Category.assoc, fv_stalkIso_hom_eq_inv (S := S) g]
  conv_rhs => rw [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem,
    Scheme.Opens.fromSpecStalkOfMem]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating `Spec.map θ ≫ pr₂` at the closed point of `A`. -/
lemma fv_eval_closedPoint (g : X.PartialMap Y) [hg : g.IsOver S] (γ : PartialMap.graph S g)
    {A : ValuationSubring X.functionField}
    (cθ : (PartialMap.graph S g).presheaf.stalk γ →+* A) (hl : IsLocalHom cθ) :
    (Spec.map (CommRingCat.ofHom cθ) ≫ (PartialMap.graph S g).fromSpecStalk γ
        ≫ PartialMap.pr₂ S g) (IsLocalRing.closedPoint A) = PartialMap.pr₂ S g γ := by
  haveI : IsLocalHom (CommRingCat.ofHom cθ).hom := hl
  conv_lhs => rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Spec_closedPoint]
  exact congrArg (PartialMap.pr₂ S g)
    (Scheme.fromSpecStalk_closedPoint (X := PartialMap.graph S g) (x := γ))

theorem fibreValue {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g] {x : X} {y₀ : Y}
    (H : ∀ (A : ValuationSubring X.functionField)
        (hA : ∀ s : X.presheaf.stalk x,
          algebraMap (X.presheaf.stalk x) X.functionField s ∈ A)
        (_ : IsLocalHom ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict
          A.toSubring hA))
        (ψ : AlgebraicGeometry.Spec (CommRingCat.of A) ⟶ Y),
        CategoryTheory.CategoryStruct.comp ψ (Work.Domain.overHom S Y) =
          CategoryTheory.CategoryStruct.comp
            (CategoryTheory.CategoryStruct.comp
              (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
                ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict A.toSubring hA)))
              (AlgebraicGeometry.Scheme.fromSpecStalk X x))
            (Work.Domain.overHom S X) →
        CategoryTheory.CategoryStruct.comp
            (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A X.functionField))) ψ =
          AlgebraicGeometry.Scheme.PartialMap.fromFunctionField g →
        ψ (IsLocalRing.closedPoint A) = y₀)
    (γ : Work.Domain.PartialMap.graph S g) (hγ : Work.Domain.PartialMap.pr₁ S g γ = x) :
    Work.Domain.PartialMap.pr₂ S g γ = y₀ := by
  subst hγ
  obtain ⟨A, hAθ, hlocθ⟩ := IsLocalRing.exists_factor_valuationRing (PartialMap.theta g γ).hom
  have hA : ∀ s : X.presheaf.stalk (PartialMap.pr₁ S g γ),
      algebraMap (X.presheaf.stalk (PartialMap.pr₁ S g γ)) X.functionField s ∈ A := by
    intro s
    rw [fv_theta_stalkMap_apply (S := S) g γ s]
    exact hAθ _
  have hcomp : ((algebraMap (X.presheaf.stalk (PartialMap.pr₁ S g γ)) X.functionField).codRestrict
        A.toSubring hA)
      = (((PartialMap.theta g γ).hom).codRestrict A.toSubring hAθ).comp
          (((PartialMap.pr₁ S g).stalkMap γ).hom) := by
    apply RingHom.ext
    intro s
    apply Subtype.ext
    exact fv_theta_stalkMap_apply (S := S) g γ s
  have hloc : IsLocalHom ((algebraMap (X.presheaf.stalk (PartialMap.pr₁ S g γ))
      X.functionField).codRestrict A.toSubring hA) := by
    rw [hcomp]
    haveI := hlocθ
    refine ⟨fun s hs => ?_⟩
    exact IsLocalHom.map_nonunit (f := ((PartialMap.pr₁ S g).stalkMap γ).hom) _
      (IsLocalHom.map_nonunit
        (f := ((PartialMap.theta g γ).hom).codRestrict A.toSubring hAθ) _ hs)
  let cθ : (PartialMap.graph S g).presheaf.stalk γ →+* A :=
    ((PartialMap.theta g γ).hom).codRestrict A.toSubring hAθ
  let ca : X.presheaf.stalk (PartialMap.pr₁ S g γ) →+* A :=
    (algebraMap (X.presheaf.stalk (PartialMap.pr₁ S g γ)) X.functionField).codRestrict
      A.toSubring hA
  have hcompC : (PartialMap.pr₁ S g).stalkMap γ ≫ CommRingCat.ofHom cθ
      = CommRingCat.ofHom ca := by
    apply CommRingCat.hom_ext_iff.mpr
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    exact hcomp.symm
  have hthetaC : CommRingCat.ofHom cθ ≫ CommRingCat.ofHom (algebraMap A X.functionField)
      = PartialMap.theta g γ := by
    ext s
    rfl
  have hpr : PartialMap.pr₂ S g ≫ (Work.Domain.overHom S Y)
      = PartialMap.pr₁ S g ≫ (Work.Domain.overHom S X) := by
    rw [PartialMap.pr₂, PartialMap.pr₁, Category.assoc, Category.assoc,
      ← pullback.condition]
  have h1 : (Spec.map (CommRingCat.ofHom cθ) ≫ (PartialMap.graph S g).fromSpecStalk γ
        ≫ PartialMap.pr₂ S g) ≫ (Work.Domain.overHom S Y)
      = (Spec.map (CommRingCat.ofHom ca) ≫ X.fromSpecStalk (PartialMap.pr₁ S g γ))
        ≫ (Work.Domain.overHom S X) := by
    calc (Spec.map (CommRingCat.ofHom cθ) ≫ (PartialMap.graph S g).fromSpecStalk γ
            ≫ PartialMap.pr₂ S g) ≫ (Work.Domain.overHom S Y)
        = Spec.map (CommRingCat.ofHom cθ)
            ≫ ((PartialMap.graph S g).fromSpecStalk γ
              ≫ (PartialMap.pr₂ S g ≫ (Work.Domain.overHom S Y))) := by
          rw [Category.assoc, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom cθ)
            ≫ ((PartialMap.graph S g).fromSpecStalk γ
              ≫ (PartialMap.pr₁ S g ≫ (Work.Domain.overHom S X))) := by
          rw [hpr]
      _ = Spec.map (CommRingCat.ofHom cθ)
            ≫ (Spec.map ((PartialMap.pr₁ S g).stalkMap γ)
              ≫ (X.fromSpecStalk (PartialMap.pr₁ S g γ)
                ≫ (Work.Domain.overHom S X))) := by
          rw [← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc (PartialMap.pr₁ S g) (x := γ)]
      _ = Spec.map (CommRingCat.ofHom ca)
            ≫ (X.fromSpecStalk (PartialMap.pr₁ S g γ) ≫ (Work.Domain.overHom S X)) := by
          rw [← Spec.map_comp_assoc]
          exact congrArg (fun t => Spec.map t
            ≫ (X.fromSpecStalk (PartialMap.pr₁ S g γ) ≫ (Work.Domain.overHom S X))) hcompC
      _ = (Spec.map (CommRingCat.ofHom ca) ≫ X.fromSpecStalk (PartialMap.pr₁ S g γ))
            ≫ (Work.Domain.overHom S X) := by
          rw [Category.assoc]
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField))
        ≫ (Spec.map (CommRingCat.ofHom cθ) ≫ (PartialMap.graph S g).fromSpecStalk γ
          ≫ PartialMap.pr₂ S g)
      = g.fromFunctionField := by
    calc Spec.map (CommRingCat.ofHom (algebraMap A X.functionField))
          ≫ (Spec.map (CommRingCat.ofHom cθ)
            ≫ ((PartialMap.graph S g).fromSpecStalk γ ≫ PartialMap.pr₂ S g))
        = (Spec.map (CommRingCat.ofHom (algebraMap A X.functionField))
            ≫ Spec.map (CommRingCat.ofHom cθ))
          ≫ ((PartialMap.graph S g).fromSpecStalk γ ≫ PartialMap.pr₂ S g) := by
          rw [← Category.assoc]
      _ = Spec.map (CommRingCat.ofHom cθ ≫ CommRingCat.ofHom (algebraMap A X.functionField))
          ≫ ((PartialMap.graph S g).fromSpecStalk γ ≫ PartialMap.pr₂ S g) := by
          rw [← Spec.map_comp]
      _ = Spec.map (PartialMap.theta g γ)
          ≫ ((PartialMap.graph S g).fromSpecStalk γ ≫ PartialMap.pr₂ S g) :=
          congrArg (fun t => Spec.map t
            ≫ ((PartialMap.graph S g).fromSpecStalk γ ≫ PartialMap.pr₂ S g)) hthetaC
      _ = g.fromFunctionField := fv_theta_fromSpecStalk (S := S) g γ
  have hψ := H A hA hloc (Spec.map (CommRingCat.ofHom cθ)
    ≫ (PartialMap.graph S g).fromSpecStalk γ ≫ PartialMap.pr₂ S g) h1 h2
  rw [← hψ]
  exact (fv_eval_closedPoint (S := S) (X := X) (Y := Y) g γ cθ hlocθ).symm

end Work.Domain.Engine
