import Mathlib
import Submission.Work.CY3.GenericPointAux
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **A `Spec`-map out of a function field followed by the generic-point map of `Y` is dominant.**
If `Y` is irreducible then `Y.fromSpecStalk (genericPoint Y)` is the map `Spec κ(Y) ⟶ Y` whose
image is the single point `genericPoint Y` (Mathlib's `Scheme.range_fromSpecStalk` says the image
is the set of points specializing to `genericPoint Y`, and in an irreducible space every point
specializing to the generic point *is* the generic point).  Hence the image of any
`Spec X.functionField ⟶ Spec Y.functionField` followed by it is `{genericPoint Y}`, which is dense
because `Y` is irreducible.  In particular no injectivity of `α` (or integrality of `Y`) is
needed. -/
lemma isDominant_specMap_fromSpecStalk {X Y : Scheme.{0}} [IrreducibleSpace Y]
    [IrreducibleSpace X] [IsIntegral X] (α : Y.functionField ⟶ X.functionField) :
    IsDominant (Spec.map α ≫ Y.fromSpecStalk (genericPoint Y)) := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  -- The range of `fromSpecStalk (genericPoint Y)` is exactly `{genericPoint Y}`.
  have hη : Set.range (Y.fromSpecStalk (genericPoint Y)) = {genericPoint Y} := by
    rw [Scheme.range_fromSpecStalk]
    ext y
    constructor
    · intro hy
      have h1 : genericPoint Y ∈ closure ({y} : Set Y) := specializes_iff_mem_closure.mp hy
      have h2 : (Set.univ : Set Y) ⊆ closure {y} :=
        (genericPoint_spec Y).mem_closed_set_iff isClosed_closure |>.mp h1
      have h3 : IsGenericPoint y (Set.univ : Set Y) := by
        rw [isGenericPoint_def]
        exact Set.eq_univ_of_univ_subset h2
      exact (h3.eq (genericPoint_spec Y))
    · intro hy
      rw [hy]
      exact specializes_refl (genericPoint Y)
  have hcomp : Set.range (Spec.map α ≫ Y.fromSpecStalk (genericPoint Y)) =
      (Y.fromSpecStalk (genericPoint Y)) '' Set.range (Spec.map α) := by
    rw [← Set.range_comp]
    rfl
  have hsub : Set.range (Spec.map α ≫ Y.fromSpecStalk (genericPoint Y)) ⊆ {genericPoint Y} := by
    rw [hcomp]
    calc (Y.fromSpecStalk (genericPoint Y)) '' Set.range (Spec.map α)
        ⊆ Set.range (Y.fromSpecStalk (genericPoint Y)) := Set.image_subset_range _ _
      _ = {genericPoint Y} := hη
  -- `Spec X.functionField` is nonempty since `X.functionField` is a field.
  obtain ⟨p⟩ := (inferInstance : Nonempty (Spec X.functionField))
  have hne : (Set.range (Spec.map α ≫ Y.fromSpecStalk (genericPoint Y))).Nonempty :=
    ⟨_, Set.mem_range_self p⟩
  have heq : Set.range (Spec.map α ≫ Y.fromSpecStalk (genericPoint Y)) = {genericPoint Y} :=
    Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨hne, fun x hx => hsub hx⟩
  rw [heq, genericPoint_closure]

theorem isDominant_ofFromSpecStalk_hom {X Y S : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (sX : X ⟶ S) (sY : Y ⟶ S) (g : Spec X.functionField ⟶ Y)
    [IsIntegral X] [LocallyOfFiniteType sY]
    (hg : g ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX)
    (α : Y.functionField ⟶ X.functionField)
    (hα : g = Spec.map α ≫ Y.fromSpecStalk (genericPoint Y)) :
    IsDominant (PartialMap.ofFromSpecStalk sX sY g hg).hom := by
  have hgd : IsDominant g := by
    rw [hα]
    exact isDominant_specMap_fromSpecStalk α
  have hfac : (PartialMap.ofFromSpecStalk sX sY g hg).domain.fromSpecStalkOfMem (genericPoint X)
        (PartialMap.mem_domain_ofFromSpecStalk sX sY g hg) ≫
        (PartialMap.ofFromSpecStalk sX sY g hg).hom = g :=
    PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY g hg
  exact IsDominant.of_comp _ _ (H := hfac ▸ hgd)

end Work.CY3
