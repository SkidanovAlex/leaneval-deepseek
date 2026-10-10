import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CrauderKatz

open CategoryTheory

/-- The projection `X ×_{Spec 𝕜} 𝔸¹ ⟶ X` has a section: the constant-zero section `x ↦ (x,0)`,
obtained from the `𝕜`-point `Spec 𝕜 ⟶ Spec 𝕜[t]` of `𝔸¹_𝕜 = Spec 𝕜[t]` corresponding to
`t ↦ 0`, i.e. `Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : 𝕜)))`.  Note
`Spec.map (t ↦ 0) ≫ Spec.map (algebraMap 𝕜 𝕜[t]) = 𝟙 _`, since `evalRingHom 0` composed with the
inclusion `𝕜 ↪ 𝕜[t]` is the identity.  Take `q := pullback.lift (𝟙 X) (f ≫ Spec.map (ofHom (evalRingHom 0))) _`
and use `pullback.lift_fst`. -/
theorem exists_section_pullback_affineLine (𝕜 : Type) [Field 𝕜] (X : AlgebraicGeometry.Scheme.{0})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :
    ∃ q : X ⟶ CategoryTheory.Limits.pullback f
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))),
      CategoryTheory.CategoryStruct.comp q (CategoryTheory.Limits.pullback.fst f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))))) =
        CategoryTheory.CategoryStruct.id X := by
  -- The composite of the two ring homs `𝕜 ↪ 𝕜[t]` and `eval 0 : 𝕜[t] → 𝕜` is the identity.
  have hcomp : CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : 𝕜)) = 𝟙 (CommRingCat.of 𝕜) := by
    ext x
    simp
  -- Hence `Spec.map (eval 0)` is a section of `Spec.map (𝕜 ↪ 𝕜[t])`.
  have hmap : AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Polynomial.evalRingHom (0 : 𝕜))) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))) =
        𝟙 (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := by
    rw [← AlgebraicGeometry.Spec.map_comp, hcomp, AlgebraicGeometry.Spec.map_id]
  -- This is exactly the commutativity required to lift `𝟙 X` and `f ≫ 0` to the pullback.
  have hw : 𝟙 X ≫ f =
      (f ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : 𝕜)))) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))) := by
    rw [Category.assoc, hmap, Category.comp_id, Category.id_comp]
  exact ⟨CategoryTheory.Limits.pullback.lift (𝟙 X)
      (f ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : 𝕜)))) hw,
    CategoryTheory.Limits.pullback.lift_fst _ _ _⟩

end Work.CrauderKatz
