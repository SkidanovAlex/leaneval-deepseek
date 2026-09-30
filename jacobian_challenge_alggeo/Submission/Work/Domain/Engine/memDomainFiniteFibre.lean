import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta
import Submission.Work.Domain.Ring
import Submission.Work.Domain.Engine.isIntegral_graph
import Submission.Work.Domain.Engine.pr1_genericPoint_facts
import Submission.Work.Domain.Engine.isIntegrallyClosed_section
import Submission.Work.Domain.Engine.exists_injective_sections_to_functionField
import Submission.Work.Domain.Engine.surjective_app_of_finite_of_isIntegrallyClosed
import Submission.Work.Domain.Engine.finite_app_of_isFinite_morphismRestrict
import Submission.Work.Domain.Engine.isIso_morphismRestrict_of_surjective_app
import Submission.Work.Domain.Engine.exists_isAffineOpen_isFinite_morphismRestrict

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.Domain.Engine

/-! ## The main theorem -/

theorem surjective_morphismRestrict {G X : Scheme.{u}} (f : G ⟶ X) (hf : Surjective f)
    (U : X.Opens) : Surjective (f ∣_ U) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨γ, hγ⟩ := hf.surj (U.ι z)
  have hγU : γ ∈ f ⁻¹ᵁ U := by
    show f γ ∈ U
    rw [hγ]
    exact z.2
  refine ⟨(⟨γ, hγU⟩ : ↥(f ⁻¹ᵁ U)), ?_⟩
  have key : U.ι ((f ∣_ U) (⟨γ, hγU⟩ : ↥(f ⁻¹ᵁ U))) = U.ι z := by
    rw [← Scheme.Hom.comp_apply (f := f ∣_ U) (g := U.ι) (x := (⟨γ, hγU⟩ : ↥(f ⁻¹ᵁ U))),
      morphismRestrict_ι, Scheme.Hom.comp_apply (f := (f ⁻¹ᵁ U).ι) (g := f)
        (x := (⟨γ, hγU⟩ : ↥(f ⁻¹ᵁ U)))]
    exact hγ
  exact (Scheme.Hom.isOpenEmbedding U.ι).injective key

theorem memDomainFiniteFibre {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g] {x : X}
    (hfin : (Work.Domain.PartialMap.pr₁ S g ⁻¹' ({x} : Set X)).Finite) :
    x ∈ g.toRationalMap.domain := by
  haveI : IsSeparated (Y ↘ S) := inferInstance
  haveI hGint : IsIntegral (Work.Domain.PartialMap.graph S g) := isIntegral_graph (S := S) g
  obtain ⟨hsurg, hgen, hstalk⟩ := pr1_genericPoint_facts (S := S) g
  obtain ⟨U, hUaff, hxU, hUfin⟩ :=
    exists_isAffineOpen_isFinite_morphismRestrict (Work.Domain.PartialMap.pr₁ S g) x hfin
  have hUdense : Dense (U : Set X) := IsOpen.dense U.2 ⟨x, hxU⟩
  haveI hUne : Nonempty ↥(U.toScheme) := ⟨⟨x, hxU⟩⟩
  have hUiso : IsIso (Work.Domain.PartialMap.pr₁ S g ∣_ U) := by
    haveI hUdom : IsDomain Γ(X, U) :=
      Function.Injective.isDomain (X.germToFunctionField U).hom
        (Scheme.germToFunctionField_injective X U)
    haveI hUfrac : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hUaff
    obtain ⟨φ, hφ, hφ'⟩ := exists_injective_sections_to_functionField (S := S) g hUaff
    have hsurjapp : Function.Surjective
        (((Work.Domain.PartialMap.pr₁ S g).app U).hom) :=
      surjective_app_of_finite_of_isIntegrallyClosed (Work.Domain.PartialMap.pr₁ S g)
        (isIntegrallyClosed_section hX hUaff) φ hφ hφ'
        (finite_app_of_isFinite_morphismRestrict _ hUaff hUfin)
    haveI : IsAffineHom (Work.Domain.PartialMap.pr₁ S g ∣_ U) := inferInstance
    haveI hUaff' : IsAffine (U.toScheme) := hUaff
    refine isIso_morphismRestrict_of_surjective_app (Work.Domain.PartialMap.pr₁ S g) hUaff ?_
      hsurjapp (surjective_morphismRestrict _ hsurg U)
    exact isAffine_of_isAffineHom (f := Work.Domain.PartialMap.pr₁ S g ∣_ U)
  haveI : IsIso (Work.Domain.PartialMap.pr₁ S g ∣_ U) := hUiso
  let hhom : U.toScheme ⟶ Y :=
    (asIso (Work.Domain.PartialMap.pr₁ S g ∣_ U)).inv ≫
      (Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι ≫ Work.Domain.PartialMap.pr₂ S g
  let h : X.PartialMap Y := ⟨U, hUdense, hhom⟩
  have heq : h.toRationalMap = g.toRationalMap := by
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ?_
    have hmul : (Work.Domain.PartialMap.pr₂ S g) ≫ (Y ↘ S) =
        (Work.Domain.PartialMap.pr₁ S g) ≫ (X ↘ S) := by
      simp only [Work.Domain.PartialMap.pr₁, Work.Domain.PartialMap.pr₂, Category.assoc,
        pullback.condition]
    have hIsOver : h.IsOver S := by
      rw [Scheme.PartialMap.isOver_iff]
      change hhom ≫ (Y ↘ S) = U.ι ≫ (X ↘ S)
      have hstep : (((Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι ≫
            Work.Domain.PartialMap.pr₂ S g) ≫ (Y ↘ S)) =
          (Work.Domain.PartialMap.pr₁ S g ∣_ U) ≫ (U.ι ≫ (X ↘ S)) := by
        rw [Category.assoc, hmul, ← Category.assoc,
          ← morphismRestrict_ι (Work.Domain.PartialMap.pr₁ S g) U, Category.assoc]
      calc hhom ≫ (Y ↘ S)
          = (asIso (Work.Domain.PartialMap.pr₁ S g ∣_ U)).inv ≫
              (((Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι ≫
                Work.Domain.PartialMap.pr₂ S g) ≫ (Y ↘ S)) := by
            simp only [hhom, Category.assoc]
        _ = (asIso (Work.Domain.PartialMap.pr₁ S g ∣_ U)).inv ≫
              ((Work.Domain.PartialMap.pr₁ S g ∣_ U) ≫ (U.ι ≫ (X ↘ S))) := by rw [hstep]
        _ = U.ι ≫ (X ↘ S) := Iso.inv_hom_id_assoc _ _
    haveI : h.IsOver S := hIsOver
    refine (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := S) (f := h) (g := g)
      (W := U ⊓ g.domain)
      (hUdense.inter_of_isOpen_right g.dense_domain g.domain.2) inf_le_left inf_le_right).mpr ?_
    change X.homOfLE (inf_le_left : U ⊓ g.domain ≤ U) ≫ hhom =
      X.homOfLE (inf_le_right : U ⊓ g.domain ≤ g.domain) ≫ g.hom
    let W : X.Opens := U ⊓ g.domain
    have hWle1 : W ≤ U := inf_le_left
    have hWle2 : W ≤ g.domain := inf_le_right
    let α : W.toScheme ⟶ (Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).toScheme :=
      X.homOfLE hWle1 ≫ (asIso (Work.Domain.PartialMap.pr₁ S g ∣_ U)).inv
    have hrange : Set.range ⇑(X.homOfLE hWle2 ≫ Work.Domain.PartialMap.toGraph S g) ⊆
        Set.range ⇑((Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι) := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      have h1 : (Work.Domain.PartialMap.pr₁ S g)
          ((X.homOfLE hWle2 ≫ Work.Domain.PartialMap.toGraph S g) w) = w.1 := by
        rw [← Scheme.Hom.comp_apply (f := X.homOfLE hWle2 ≫ Work.Domain.PartialMap.toGraph S g)
          (g := Work.Domain.PartialMap.pr₁ S g) (x := w), Category.assoc,
          Work.Domain.PartialMap.toGraph_pr₁, Scheme.homOfLE_ι]
        rfl
      show (Work.Domain.PartialMap.pr₁ S g)
        ((X.homOfLE hWle2 ≫ Work.Domain.PartialMap.toGraph S g) w) ∈ U
      rw [h1]
      exact hWle1 w.2
    let β : W.toScheme ⟶ (Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).toScheme :=
      IsOpenImmersion.lift ((Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι)
        (X.homOfLE hWle2 ≫ Work.Domain.PartialMap.toGraph S g) hrange
    have hβ : β ≫ (Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι =
        X.homOfLE hWle2 ≫ Work.Domain.PartialMap.toGraph S g :=
      IsOpenImmersion.lift_fac ..
    have hαβ : α = β := by
      have hα : α ≫ (Work.Domain.PartialMap.pr₁ S g ∣_ U) = X.homOfLE hWle1 := by
        show (X.homOfLE hWle1 ≫
            (asIso (Work.Domain.PartialMap.pr₁ S g ∣_ U)).inv) ≫
          (asIso (Work.Domain.PartialMap.pr₁ S g ∣_ U)).hom = X.homOfLE hWle1
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have hβ' : β ≫ (Work.Domain.PartialMap.pr₁ S g ∣_ U) = X.homOfLE hWle1 := by
        rw [← cancel_mono U.ι]
        calc (β ≫ (Work.Domain.PartialMap.pr₁ S g ∣_ U)) ≫ U.ι
            = β ≫ ((Work.Domain.PartialMap.pr₁ S g ∣_ U) ≫ U.ι) := Category.assoc _ _ _
          _ = β ≫ ((Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι ≫
                Work.Domain.PartialMap.pr₁ S g) := by
              rw [morphismRestrict_ι (Work.Domain.PartialMap.pr₁ S g) U]
          _ = (β ≫ (Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι) ≫
                Work.Domain.PartialMap.pr₁ S g := (Category.assoc _ _ _).symm
          _ = (X.homOfLE hWle2 ≫ Work.Domain.PartialMap.toGraph S g) ≫
                Work.Domain.PartialMap.pr₁ S g := by rw [hβ]
          _ = X.homOfLE hWle2 ≫ (Work.Domain.PartialMap.toGraph S g ≫
                Work.Domain.PartialMap.pr₁ S g) := Category.assoc _ _ _
          _ = X.homOfLE hWle2 ≫ g.domain.ι := by rw [Work.Domain.PartialMap.toGraph_pr₁]
          _ = X.homOfLE hWle1 ≫ U.ι := by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
      exact (cancel_mono (Work.Domain.PartialMap.pr₁ S g ∣_ U)).mp (hα.trans hβ'.symm)
    calc (X.homOfLE hWle1 ≫ hhom)
        = α ≫ (Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι ≫ Work.Domain.PartialMap.pr₂ S g := by
          show (X.homOfLE hWle1 ≫ ((asIso (Work.Domain.PartialMap.pr₁ S g ∣_ U)).inv ≫
            (Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι ≫ Work.Domain.PartialMap.pr₂ S g)) = _
          simp only [α, Category.assoc]
      _ = β ≫ (Work.Domain.PartialMap.pr₁ S g ⁻¹ᵁ U).ι ≫ Work.Domain.PartialMap.pr₂ S g := by
          rw [hαβ]
      _ = X.homOfLE hWle2 ≫ g.hom := by
          rw [← Category.assoc, hβ, Category.assoc, Work.Domain.PartialMap.toGraph_pr₂]
  exact Scheme.RationalMap.mem_domain.mpr ⟨h, hxU, heq⟩

end Work.Domain.Engine
