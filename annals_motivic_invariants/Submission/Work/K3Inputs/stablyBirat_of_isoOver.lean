import Mathlib
import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **Isomorphic `𝕜`-schemes are stably birational.**

From an isomorphism `e : X ≅ Y` over `Spec 𝕜` one gets `X × 𝔸⁰ ≅ Y × 𝔸⁰`; since
`𝔸(Fin 0; Spec 𝕜) ≅ Spec 𝕜` (Mathlib's `AlgebraicGeometry.AffineSpace.SpecIso` at `Fin 0`,
`MvPolynomial (Fin 0) 𝕜 ≅ 𝕜`), the products are the two schemes again, so `StablyBirat 𝕜 X Y`
holds with exponents `0, 0`.  This is the base case used to compare the stable birationality of
the centres of two models of the K3 L-link. -/
theorem stablyBirat_of_isoOver (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}}
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (h : Work.K3.IsoOver 𝕜 X Y) :
    Work.K3Inputs.StablyBirat 𝕜 X Y := by
  obtain ⟨e, he⟩ := h
  -- The isomorphism is over the base, so it commutes with the structure morphisms.
  have he' : e.hom ≫ (Y ↘ Spec (.of 𝕜)) = (X ↘ Spec (.of 𝕜)) :=
    (Hom.isOver_iff (X := X) (Y := Y) (S := Spec (.of 𝕜))).mp he
  -- The induced map of fibre products `X × 𝔸⁰ ⟶ Y × 𝔸⁰` is an isomorphism, since all three
  -- components of the cospan morphism are (`pullback.map_isIso`).
  have hIso : IsIso (pullback.map (X ↘ Spec (.of 𝕜)) (AffineN 𝕜 0 ↘ Spec (.of 𝕜))
      (Y ↘ Spec (.of 𝕜)) (AffineN 𝕜 0 ↘ Spec (.of 𝕜)) e.hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact he'.symm) (by simp)) := inferInstance
  -- Exponent `0` in both stable birationality slots: `X × 𝔸⁰ ≅ Y × 𝔸⁰`.
  let F : Work.K3.prodOver 𝕜 X (AffineN 𝕜 0) ⟶ Work.K3.prodOver 𝕜 Y (AffineN 𝕜 0) :=
    pullback.map (X ↘ Spec (.of 𝕜)) (AffineN 𝕜 0 ↘ Spec (.of 𝕜))
      (Y ↘ Spec (.of 𝕜)) (AffineN 𝕜 0 ↘ Spec (.of 𝕜)) e.hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact he'.symm) (by simp)
  haveI : IsIso F := hIso
  exact ⟨0, 0, ⟨Scheme.PartialIso.ofIso (asIso F)⟩⟩

end Work.K3Inputs
