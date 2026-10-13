import Mathlib
import Submission.Work.DSG2.Defs
import Submission.Work.DSG2.ExistsImmersionAux.Defs
import Submission.Work.DSG2.exists_chartRingSurj_u

/-!
# DSG2: a surjection `A[x₀,…,x_N] ↠ Γ(X, U)` produces an immersion `U ↪ ℙᴺ_A`

`Work.DSG2.immersionPSpaceOfSurj`: suppose `U ⊆ X` is an affine open of a scheme `X` over
`Spec A`, and suppose we are given a *surjective* ring map

  `ψ : A[x₀,…,x_N] →+* Γ(X, U)`

which is a map of `A`-algebras for the `A`-structure `sectionAlgebra f U` induced by `f`
(i.e. `ψ ∘ C = sectionAlgebra f U`).  Then `U` embeds into the projective space `ℙᴺ_A` as an
immersion over `Spec A`.

This is the "already given presentation" form of `Work.DSG2.exists_immersion_pspace_u`: there
the surjection is produced from finite-typeness of `Γ(X, U)`; here it is an input, which is
what the Chow construction needs (the presentation is fixed in advance by the choice of the
affine cover).

The proof is the same as for `exists_immersion_pspace_u`: `ψ` exhibits `Spec Γ(X, U)` as a
closed subscheme of `𝔸^N_A = Spec A[x₀,…,x_N]`, and the standard open chart
`Spec A[y₀,…,y_{N-1}] ≅ D₊(x₀) ↪ ℙᴺ_A` (`Work.DSG2.chartι`) composes with it to the desired
immersion.  The structure morphisms agree because `ψ` is a map of `A`-algebras.
-/

namespace Work.DSG2

open CategoryTheory AlgebraicGeometry

universe u

-- The `haveI` below registers a typeclass instance (`IsImmersion` is used through typeclass
-- search in `IsImmersion.comp`), so the style linter's suggestion to use `have` does not apply.
set_option linter.style.haveILetI false

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The composite `Spec Γ(X,U) → Spec A` of the affine-open immersion with `f` corresponds to the
`A`-algebra structure induced on `Γ(X,U)` by `f`. -/
theorem fromSpec_comp_sectionAlgebra_ofSurj {A : Type u} [CommRing A]
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (U : X.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    hU.fromSpec ≫ f = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (sectionAlgebra f U)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f
    (isAffineOpen_top (Spec (CommRingCat.of A))) hU (le_top : U ≤ f ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h]
  rw [sectionAlgebra]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp]
  rfl

theorem immersionPSpaceOfSurj (A : Type*) [CommRing A] {X : AlgebraicGeometry.Scheme}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) (N : ℕ)
    (ψ : MvPolynomial (Fin N) A →+* X.presheaf.obj (Opposite.op U))
    (hψ : Function.Surjective ψ)
    (hC : ψ.comp MvPolynomial.C = Work.DSG2.sectionAlgebra f U) :
    ∃ i : (U : AlgebraicGeometry.Scheme) ⟶ DSMap.PSpace A N,
      AlgebraicGeometry.IsImmersion i ∧
        CategoryTheory.CategoryStruct.comp i (DSMap.PSpace.toSpec A N) =
          CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Scheme.Opens.ι U) f := by
  -- a surjection from the standard chart ring of `ℙᴺ_A` onto `A[x₀,…,x_N]`, compatible with
  -- the constants of the chart
  obtain ⟨ψ₀, hψ₀surj, hψ₀alg⟩ := exists_chartRingSurj_u A N 0
  have hsurj : Function.Surjective (ψ.comp ψ₀) := hψ.comp hψ₀surj
  haveI hcmp : IsClosedImmersion (Spec.map (CommRingCat.ofHom (ψ.comp ψ₀))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  refine ⟨hU.isoSpec.hom ≫ (Spec.map (CommRingCat.ofHom (ψ.comp ψ₀)) ≫ chartι A N 0), ?_, ?_⟩
  · exact IsImmersion.comp _ _
  · -- the presentation is a map of `A`-algebras, so the structure morphisms agree
    have hψ₀C : ψ₀.comp (chartAto A N 0) = MvPolynomial.C :=
      RingHom.ext fun a => by rw [RingHom.comp_apply]; exact hψ₀alg a
    have hkey : (ψ.comp ψ₀).comp (chartAto A N 0) = ψ.comp MvPolynomial.C := by
      rw [RingHom.comp_assoc, hψ₀C]
    calc (hU.isoSpec.hom ≫ (Spec.map (CommRingCat.ofHom (ψ.comp ψ₀)) ≫
            chartι A N 0)) ≫ DSMap.PSpace.toSpec A N
        = hU.isoSpec.hom ≫ (Spec.map (CommRingCat.ofHom (ψ.comp ψ₀)) ≫
            (chartι A N 0 ≫ DSMap.PSpace.toSpec A N)) := by simp only [Category.assoc]
      _ = hU.isoSpec.hom ≫ (Spec.map (CommRingCat.ofHom (ψ.comp ψ₀)) ≫
            Spec.map (CommRingCat.ofHom (chartAto A N 0))) := by rw [chartι_toSpec]
      _ = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
            ((ψ.comp ψ₀).comp (chartAto A N 0))) := by
            rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      _ = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (ψ.comp MvPolynomial.C)) := by
            rw [hkey]
      _ = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (sectionAlgebra f U)) := by rw [hC]
      _ = hU.isoSpec.hom ≫ (hU.fromSpec ≫ f) := by
            rw [← fromSpec_comp_sectionAlgebra_ofSurj f U hU]
      _ = (hU.isoSpec.hom ≫ hU.fromSpec) ≫ f := by rw [Category.assoc]
      _ = U.ι ≫ f := by rw [IsAffineOpen.isoSpec_hom_fromSpec]

end Work.DSG2
