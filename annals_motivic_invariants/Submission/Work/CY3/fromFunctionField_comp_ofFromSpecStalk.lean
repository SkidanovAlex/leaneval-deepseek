import Mathlib
import Submission.Work.CY3.GenericPointAux
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fromFunctionField` of a composite of partial maps

This module contains the auxiliary lemma `Work.CY3.fromFunctionField_comp_general`, expressing the
generic-point morphism of a composite `f.comp h` of partial maps, and the requested statement
`Work.CY3.fromFunctionField_comp_ofFromSpecStalk`.

* If `f : X.PartialMap Y` (with `f.hom` dominant) and `h : Y.PartialMap Z`, and the generic-point
  morphism of `f` factors as `Spec.map α` followed by the generic-point morphism of `Y`, then the
  generic-point morphism of `f.comp h` is `Spec.map α` followed by the generic-point morphism of
  `h`.  This is the compatibility of `PartialMap.fromFunctionField` with `PartialMap.comp`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.CY3

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **`fromFunctionField` is compatible with composition of partial maps.**
Let `f : X.PartialMap Y` be a partial map whose underlying morphism is dominant, let
`h : Y.PartialMap Z`, and suppose that the generic-point morphism of `f` factors as
`Spec.map α` followed by the generic-point morphism `Spec K(Y) ⟶ Y` of `Y`.  Then the
generic-point morphism of `f.comp h` is obtained by first applying `Spec.map α` and then the
generic-point morphism of `h`.  (The proof only uses that `X` and `Y` are irreducible.) -/
theorem fromFunctionField_comp_general {X Y Z : Scheme} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (h : Y.PartialMap Z)
    (α : Y.functionField ⟶ X.functionField)
    (hα : f.fromFunctionField = Spec.map α ≫ Y.fromSpecStalk (genericPoint Y)) :
    (f.comp h).fromFunctionField = Spec.map α ≫ h.fromFunctionField := by
  have hstep : (Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ h.domain)).inv ≫ (f.hom ⁻¹ᵁ h.domain).ι
      = X.homOfLE (Opens.ι_image_le f.domain (f.hom ⁻¹ᵁ h.domain)) :=
    Opens.isoImage_ι_inv_ι f.domain (f.hom ⁻¹ᵁ h.domain)
  have hstepR : (Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ h.domain)).inv
        ≫ ((f.hom ∣_ h.domain) ≫ h.domain.ι)
      = X.homOfLE (Opens.ι_image_le f.domain (f.hom ⁻¹ᵁ h.domain)) ≫ f.hom := by
    rw [morphismRestrict_ι, ← Category.assoc, hstep]
  have claim1 : ∀ (h1 : genericPoint X ∈ f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ h.domain)),
      (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ h.domain)).fromSpecStalkOfMem (genericPoint X) h1
          ≫ X.homOfLE (Opens.ι_image_le f.domain (f.hom ⁻¹ᵁ h.domain))
        = f.domain.fromSpecStalkOfMem (genericPoint X)
            ((Opens.ι_image_le f.domain (f.hom ⁻¹ᵁ h.domain)) h1) := by
    intro h1
    apply (cancel_mono f.domain.ι).mp
    rw [Category.assoc, homOfLE_ι, Opens.fromSpecStalkOfMem_ι, Opens.fromSpecStalkOfMem_ι]
  have hpre : ∀ (h1 : genericPoint X ∈ f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ h.domain))
      (h3 : genericPoint Y ∈ h.domain),
      (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ h.domain)).fromSpecStalkOfMem (genericPoint X) h1
          ≫ (Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ h.domain)).inv ≫ (f.hom ∣_ h.domain)
        = Spec.map α ≫ h.domain.fromSpecStalkOfMem (genericPoint Y) h3 := by
    intro h1 h3
    apply (cancel_mono h.domain.ι).mp
    simp only [Category.assoc]
    rw [hstepR]
    conv_lhs => rw [← Category.assoc]
    rw [claim1 h1]
    rw [Opens.fromSpecStalkOfMem_ι]
    exact hα
  have hcomp : f.comp h = ⟨f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ h.domain), (f.comp h).dense_domain,
      (Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ h.domain)).inv ≫ (f.hom ∣_ h.domain) ≫ h.hom⟩ := rfl
  rw [hcomp]
  simp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem]
  conv_lhs => rw [← Category.assoc]
  conv_lhs => rw [← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  apply congrArg (· ≫ h.hom)
  rw [Category.assoc]
  exact hpre _ _

theorem fromFunctionField_comp_ofFromSpecStalk {X Y Z S : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (sX : X ⟶ S) (sY : Y ⟶ S) (g : Spec X.functionField ⟶ Y)
    [IsIntegral X] [LocallyOfFiniteType sY]
    (hg : g ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX)
    (h : Y.PartialMap Z) (α : Y.functionField ⟶ X.functionField)
    (hα : g = Spec.map α ≫ Y.fromSpecStalk (genericPoint Y))
    [IsDominant (PartialMap.ofFromSpecStalk sX sY g hg).hom] :
    ((PartialMap.ofFromSpecStalk sX sY g hg).comp h).fromFunctionField =
      Spec.map α ≫ h.fromFunctionField := by
  have hFF : (PartialMap.ofFromSpecStalk sX sY g hg).fromFunctionField = g :=
    PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY g hg
  exact fromFunctionField_comp_general (PartialMap.ofFromSpecStalk sX sY g hg) h α (hFF.trans hα)

end Work.CY3
