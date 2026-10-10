import Mathlib
import Submission.Work.CY3Stab.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.algMapResidue` — the structure map `𝕜 ⟶ κ(y)` of a `𝕜`-scheme

For a scheme `Y` over `Spec 𝕜` and a point `y : Y`, the residue field `κ(y)` is a `𝕜`-algebra;
the structure map is the composite

`𝕜 ≅ Γ(Spec 𝕜, ⊤) ⟶ Γ(Y, ⊤) ⟶ κ(y)`

of the inverse of `Scheme.ΓSpecIso` with the pullback of global sections along `Y ⟶ Spec 𝕜` and
the evaluation `Scheme.Γevaluation y`.

This module records the definition and its basic functoriality, which is the vocabulary in which
the residue-field computations of the CY3 stabilisation are stated.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [CommRing 𝕜]

/-- **The structure map `𝕜 ⟶ κ(y)`** of a scheme `Y` over `Spec 𝕜` at a point `y`, i.e.

`𝕜 → Γ(Spec 𝕜, ⊤) → Γ(Y, ⊤) → κ(y)`. -/
noncomputable def algMapResidue {Y : Scheme.{0}} (h : Y ⟶ Spec (CommRingCat.of 𝕜)) (y : Y) :
    CommRingCat.of 𝕜 ⟶ Y.residueField y :=
  (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ h.appTop ≫ Y.Γevaluation y

/-- Naturality of `algMapResidue` in the scheme. -/
theorem algMapResidue_naturality {Y Z : Scheme.{0}} (p : Y ⟶ Z)
    (h : Z ⟶ Spec (CommRingCat.of 𝕜)) (y : Y) :
    algMapResidue (p ≫ h) y = algMapResidue h (p y) ≫ p.residueFieldMap y := by
  simp only [algMapResidue, Scheme.Hom.comp_appTop, Category.assoc]
  rw [Scheme.Γevaluation_naturality p y]

/-- `algMapResidue` of the identity morphism `Spec 𝕜 ⟶ Spec 𝕜`. -/
theorem algMapResidue_id {Y : Scheme.{0}} (h : Y ⟶ Spec (CommRingCat.of 𝕜)) (y : Y) :
    algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜))) (h y) ≫ h.residueFieldMap y =
      algMapResidue h y := by
  have := algMapResidue_naturality (𝕜 := 𝕜) h (𝟙 (Spec (CommRingCat.of 𝕜))) y
  rw [Category.comp_id] at this
  exact this.symm

/-- `algMapResidue` of `Spec.map`. -/
theorem algMapResidue_specMap {A : Type} [CommRing A] (ψ : CommRingCat.of 𝕜 ⟶ CommRingCat.of A)
    (y : Spec (CommRingCat.of A)) :
    algMapResidue (Spec.map ψ) y = ψ ≫ algMapResidue (𝟙 (Spec (CommRingCat.of A))) y := by
  simp only [algMapResidue, Scheme.Hom.id_appTop, Category.id_comp, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality ψ]

/-- `algMapResidue` is compatible with the canonical isomorphism of residue fields of equal
points of `Spec 𝕜`. -/
theorem algMapResidue_residueFieldCongr {y₁ y₂ : Spec (CommRingCat.of 𝕜)} (e : y₁ = y₂) :
    algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜))) y₁
        ≫ ((Spec (CommRingCat.of 𝕜)).residueFieldCongr e).hom =
      algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜))) y₂ := by
  subst e
  simp [algMapResidue]

end

end Work.CY3Stab.Prod
