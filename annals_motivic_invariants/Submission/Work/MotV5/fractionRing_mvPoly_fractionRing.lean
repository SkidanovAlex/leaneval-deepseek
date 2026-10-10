import Mathlib

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotV5

section

set_option linter.style.haveILetI false

-- `MvPolynomial.isLocalization` is stated for the (deliberately non-global) base-change algebra
-- structure `MvPolynomial.algebraMvPolynomial`.  Registering that very definition as a *local*
-- instance makes typeclass search find it, and pins the algebra argument occurring in the
-- conclusion of `MvPolynomial.isLocalization` to that exact term.
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- **Fraction fields of `MvPolynomial` do not see the base change to the fraction field.**

For a domain `R` that is a `𝕜`-algebra and any index type `σ`, the fraction field of the polynomial
ring `R[X_σ]` agrees with that of `FractionRing R [X_σ]`: both are localizations of
`MvPolynomial σ R` at submonoids of non-zero-divisors (`FractionRing R` is a localization of `R`, so
`MvPolynomial σ (FractionRing R)` is a localization of `MvPolynomial σ R` by
`MvPolynomial.isLocalization`, and two localizations at submonoids of non-zero-divisors have the
same fraction field via `IsFractionRing.isFractionRing_of_isLocalization` and
`IsLocalization.algEquiv`).  Watch out: `MvPolynomial.isLocalization` is registered with the
`algebraMvPolynomial` structure as a *local* instance, so the base-change algebra structure has to
be introduced with `letI`/`haveI`. -/
theorem fractionRing_mvPoly_fractionRing {𝕜 R : Type} [Field 𝕜] [CommRing R] [IsDomain R]
    [Algebra 𝕜 R] (σ : Type) :
    Nonempty (FractionRing (MvPolynomial σ (FractionRing R)) ≃ₐ[𝕜] FractionRing (MvPolynomial σ R)) := by
  -- `MvPolynomial σ (FractionRing R)` is the localization of `MvPolynomial σ R` away from the
  -- image of the non-zero-divisors of `R`, which are non-zero-divisors of `MvPolynomial σ R`.
  have hle : (nonZeroDivisors R).map (MvPolynomial.C (σ := σ)) ≤
      nonZeroDivisors (MvPolynomial σ R) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) (MvPolynomial.C_injective σ R (by simpa using h))
  -- The canonical `MvPolynomial σ (FractionRing R)`-algebra structure on `FractionRing (MvPolynomial σ R)`.
  letI hST : Algebra (MvPolynomial σ (FractionRing R))
      (FractionRing (MvPolynomial σ R)) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _
      (nonZeroDivisors (MvPolynomial σ R)) hle
  haveI hSTtower : IsScalarTower (MvPolynomial σ R) (MvPolynomial σ (FractionRing R))
      (FractionRing (MvPolynomial σ R)) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _
      (nonZeroDivisors (MvPolynomial σ R)) hle
  -- `FractionRing (MvPolynomial σ R)` is also a fraction ring of `MvPolynomial σ (FractionRing R)`.
  have hFracS : IsFractionRing (MvPolynomial σ (FractionRing R))
      (FractionRing (MvPolynomial σ R)) :=
    IsFractionRing.isFractionRing_of_isLocalization _ _ _ hle
  -- The base-change algebra structure is compatible with the `𝕜`-algebra structures.
  have key1 : (algebraMap 𝕜 (MvPolynomial σ R)) =
      (MvPolynomial.C (σ := σ)).comp (algebraMap 𝕜 R) := by
    ext x; rw [AddMonoidAlgebra.coe_algebraMap]; rfl
  have key2 : (algebraMap 𝕜 (MvPolynomial σ (FractionRing R))) =
      (MvPolynomial.C (σ := σ)).comp (algebraMap 𝕜 (FractionRing R)) := by
    ext x; rw [AddMonoidAlgebra.coe_algebraMap]; rfl
  haveI hst𝕜AS : IsScalarTower 𝕜 (MvPolynomial σ R) (MvPolynomial σ (FractionRing R)) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [key2, key1, RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.algebraMap_def,
      MvPolynomial.map_C, IsScalarTower.algebraMap_apply 𝕜 R (FractionRing R)]
  haveI hst𝕜ST : IsScalarTower 𝕜 (MvPolynomial σ (FractionRing R))
      (FractionRing (MvPolynomial σ R)) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [IsScalarTower.algebraMap_apply 𝕜 (MvPolynomial σ R) (MvPolynomial σ (FractionRing R)),
      ← IsScalarTower.algebraMap_apply (MvPolynomial σ R) (MvPolynomial σ (FractionRing R))
        (FractionRing (MvPolynomial σ R)),
      IsScalarTower.algebraMap_apply 𝕜 (MvPolynomial σ R) (FractionRing (MvPolynomial σ R))]
  -- Two fraction rings of the same domain are canonically isomorphic, and the isomorphism is
  -- `𝕜`-linear because all the algebra structures form towers over `𝕜`.
  exact ⟨AlgEquiv.restrictScalars 𝕜
    (FractionRing.algEquiv (MvPolynomial σ (FractionRing R)) (FractionRing (MvPolynomial σ R)))⟩

end

end Work.MotV5
