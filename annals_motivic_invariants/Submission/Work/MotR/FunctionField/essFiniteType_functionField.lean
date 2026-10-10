/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotR.FunctionField
-/
import Mathlib
import Submission.Work.FFResidual.All
import Submission.Work.MotR.Defs
import Submission.Work.MotR.Transcendental.Defs
import Submission.Work.MotR.Transcendental.isScalarTower_overSectionAlgebra_overFunctionFieldAlgebra

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# The function field of a variety is essentially of finite type over the constants

For `X` a variety over a field `𝔽` (an irreducible reduced separated scheme of finite type over
`Spec 𝔽`) the function field `X.functionField = 𝒪_{X, η}` is, via the structure map
`𝔽 → Γ(X, ⊤) → X.functionField` of `Work.FFResidual.overFunctionFieldAlgebra`, an essentially
finite type `𝔽`-algebra:

`Work.MotR.FunctionField.essFiniteType_functionField`.

This is the input the function-field classes (b)–(d) of Lin–Shinder, *Motivic invariants of
birational maps*, Annals of Math. **199** (1), 2024 use without comment (a function field of a
variety is a finitely generated field extension of its field of constants); in this workspace it
feeds `Work.MotR.FunctionField.hasFunctionFieldPlace_of_perfect_essFiniteType` (the separating
transcendence basis of `Work.MotR.Transcendental.exists_algebraicIndependent_moduleFinite` needs
the finite generation).

## The route

Pick a nonempty affine open chart `U ⊆ X`; write `A = Γ(X, U)`. Then

* `A` is a finitely generated `𝔽`-algebra (`finiteType_overSectionAlgebra`), because
  `Spec A ≅ U → X → Spec 𝔽` is a locally-finite-type morphism of affine schemes,
  `HasRingHomProperty.Spec_iff` turns this into finite type of the structure hom
  `𝔽 → Γ(Spec 𝔽, ⊤) ≅ Γ(X, U)`;
* `X.functionField = Frac A`: `functionField_isFractionRing_of_isAffineOpen` identifies the
  function field with the fraction field of the section ring of any affine open;
* the constants act compatibly: `IsScalarTower 𝔽 A X.functionField` is
  `Work.MotR.Transcendental.isScalarTower_overSectionAlgebra_overFunctionFieldAlgebra`.

An essentially finite type algebra is a localization of a finite type algebra
(`Algebra.EssFiniteType.of_finiteType`, `Algebra.EssFiniteType.of_isLocalization`), and
essential finiteness of type is preserved by composition
(`Algebra.EssFiniteType.comp`), so the composite `𝔽 → A → X.functionField` is essentially of
finite type.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory

namespace Work.MotR.FunctionField

/-- **The section ring of an affine open of a scheme locally of finite type over `𝔽` is a
finitely generated `𝔽`-algebra**, for the algebra structure `𝔽 → Γ(X, ⊤) → Γ(X, U)` of
`Work.MotR.Transcendental.overSectionAlgebra`.

The ring hom `ψ : 𝔽 ⟶ Γ(X, U)` through which `overSectionAlgebra` factors agrees with the
structure map of the affine chart: `Spec.map ψ = hU.fromSpec ≫ (X ↘ Spec 𝔽)`
(`IsAffineOpen.SpecMap_appLE_fromSpec`, together with `Scheme.Hom.appLE = appTop ≫ restriction`).
The composite `Spec Γ(X, U) ≅ U → X → Spec 𝔽` is locally of finite type (an open immersion
composed with the locally-finite-type structure morphism), and for an affine source this is
finite type of the ring hom (`HasRingHomProperty.Spec_iff`). -/
theorem finiteType_overSectionAlgebra (𝔽 : Type) [Field 𝔽] (X : AlgebraicGeometry.Scheme)
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝔽))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝔽))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := Work.MotR.Transcendental.overSectionAlgebra 𝔽 X U
    Algebra.FiniteType 𝔽 Γ(X, U) := by
  letI := Work.MotR.Transcendental.overSectionAlgebra 𝔽 X U
  -- the structure ring hom `𝔽 → Γ(X, U)` through which `overSectionAlgebra` factors
  let ψ : CommRingCat.of 𝔽 ⟶ X.presheaf.obj (Opposite.op U) :=
    (Scheme.ΓSpecIso (CommRingCat.of 𝔽)).inv ≫
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝔽)).appTop ≫
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
  -- `U ≤ f ⁻¹ᵁ ⊤` for `f` the structure morphism (both sides are `⊤`)
  have hle : U ≤ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝔽)) ⁻¹ᵁ ⊤ := le_top
  -- the same hom, with the restriction to `U` bundled into `Scheme.Hom.appLE`
  have hψ : ψ = (Scheme.ΓSpecIso (CommRingCat.of 𝔽)).inv ≫
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝔽)).appLE ⊤ U hle := by
    dsimp only [ψ]
    rw [Scheme.Hom.appLE]
    congr 1
  -- and `Spec.map ψ` is the structure morphism of the affine chart
  have htop : (isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of 𝔽))).fromSpec
      = (AlgebraicGeometry.Spec (CommRingCat.of 𝔽)).isoSpec.inv :=
    IsAffineOpen.fromSpec_top
  have hmap : Spec.map ψ = hU.fromSpec ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝔽)) := by
    rw [hψ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← htop,
      IsAffineOpen.SpecMap_appLE_fromSpec _ (isAffineOpen_top _) hU hle]
  -- an open immersion composed with a locally finite type morphism is locally of finite type
  haveI : LocallyOfFiniteType (Spec.map ψ) := by rw [hmap]; infer_instance
  -- for an affine source, locally of finite type is finite type of the ring hom
  have hft : RingHom.FiniteType ψ.hom :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (R := CommRingCat.of 𝔽) (S := X.presheaf.obj (Opposite.op U))
      (φ := ψ)).mp ‹LocallyOfFiniteType (Spec.map ψ)›
  exact hft

/-- **The function field of an `𝔽`-variety is essentially of finite type over `𝔽`.**

Take a nonempty affine open `U ⊆ X`, so that `A = Γ(X, U)` is a finitely generated `𝔽`-algebra
(`finiteType_overSectionAlgebra`) and `X.functionField = Frac A`
(`functionField_isFractionRing_of_isAffineOpen`); the constants act compatibly, and essential
finiteness of type is preserved by localization and composition. -/
theorem essFiniteType_functionField (𝔽 : Type) [Field 𝔽] (X : AlgebraicGeometry.Scheme) [MotivicInvariants.Variety 𝔽 X] : (letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X; Algebra.EssFiniteType 𝔽 X.functionField) := by
  letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X
  haveI : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of 𝔽)) :=
    MotivicInvariants.Variety.locallyOfFiniteType
  -- a nonempty affine open chart `U ⊆ X`; `X` is nonempty since it is irreducible
  obtain ⟨x⟩ : Nonempty X := inferInstance
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hUaff : IsAffineOpen U := isAffineOpen_opensRange _
  have hxU : x ∈ U := X.affineCover.covers x
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  -- the section ring of the chart is a finitely generated `𝔽`-algebra
  letI : Algebra 𝔽 Γ(X, U) := Work.MotR.Transcendental.overSectionAlgebra 𝔽 X U
  haveI : Algebra.FiniteType 𝔽 Γ(X, U) := finiteType_overSectionAlgebra 𝔽 X U hUaff
  haveI : Algebra.EssFiniteType 𝔽 Γ(X, U) :=
    Algebra.EssFiniteType.of_finiteType 𝔽 ↥Γ(X, U)
  -- and a localization of it: the function field is the fraction field of the chart
  haveI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hUaff
  haveI : Algebra.EssFiniteType Γ(X, U) X.functionField :=
    Algebra.EssFiniteType.of_isLocalization ↥X.functionField (nonZeroDivisors ↥Γ(X, U))
  -- the two algebra structures are compatible
  haveI : IsScalarTower 𝔽 Γ(X, U) X.functionField :=
    Work.MotR.Transcendental.isScalarTower_overSectionAlgebra_overFunctionFieldAlgebra 𝔽 X U
  exact Algebra.EssFiniteType.comp 𝔽 Γ(X, U) X.functionField

end Work.MotR.FunctionField
