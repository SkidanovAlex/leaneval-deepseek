import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotV5

/-! ### Fraction fields of polynomial rings do not see the fraction field of the coefficients

We prove the general "Frac(Frac) = Frac" statement for `MvPolynomial`: for a domain `R` and an
index type `σ`,
`FractionRing (MvPolynomial σ (FractionRing R)) ≃ₐ[𝕜] FractionRing (MvPolynomial σ R)`.
The point is that `MvPolynomial σ (FractionRing R)` is the localization of `MvPolynomial σ R` at
the image of the non-zero-divisors of `R` (instance `MvPolynomial.isLocalization`), and that
localizing a localization yields the same fraction field
(`IsLocalization.localization_localization_isLocalization_of_has_all_units`, which describes the
composite localization as the localization at the preimage of the non-zero-divisors of the middle
ring; here that preimage is exactly the set of non-zero-divisors of `MvPolynomial σ R`), after
which `IsLocalization.algEquiv` compares the two localizations.

Watch out: `MvPolynomial.isLocalization` is registered with the `algebraMvPolynomial` structure as
a *local* instance, so the base-change algebra structure has to be introduced with `letI`. -/

/-- **Fraction fields of `MvPolynomial` do not see the base change to the fraction field.**

For a domain `R` that is a `𝕜`-algebra and any index type `σ`, the fraction field of the polynomial
ring `R[X_σ]` agrees with that of `FractionRing R [X_σ]`. -/
theorem nonempty_fractionRing_mvPolynomial_fractionRing {𝕜 R : Type} [Field 𝕜] [CommRing R]
    [IsDomain R] [Algebra 𝕜 R] (σ : Type) :
    Nonempty (FractionRing (MvPolynomial σ (FractionRing R)) ≃ₐ[𝕜] FractionRing (MvPolynomial σ R)) := by
  letI : Algebra (MvPolynomial σ R) (MvPolynomial σ (FractionRing R)) :=
    MvPolynomial.algebraMvPolynomial
  haveI hloc : IsLocalization ((nonZeroDivisors R).map MvPolynomial.C)
      (MvPolynomial σ (FractionRing R)) :=
    MvPolynomial.isLocalization (nonZeroDivisors R) (FractionRing R)
  -- The composite localization of `MvPolynomial σ R` is the localization at the preimage of the
  -- non-zero-divisors of `MvPolynomial σ (FractionRing R)`.
  have hN : IsLocalization ((nonZeroDivisors (MvPolynomial σ (FractionRing R))).comap
        (algebraMap (MvPolynomial σ R) (MvPolynomial σ (FractionRing R))))
      (FractionRing (MvPolynomial σ (FractionRing R))) :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      (R := MvPolynomial σ R) (M := (nonZeroDivisors R).map MvPolynomial.C)
      (S := MvPolynomial σ (FractionRing R))
      (N := nonZeroDivisors (MvPolynomial σ (FractionRing R)))
      (T := FractionRing (MvPolynomial σ (FractionRing R)))
      (fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero)
  have hinj :
      Function.Injective (algebraMap (MvPolynomial σ R) (MvPolynomial σ (FractionRing R))) :=
    FaithfulSMul.algebraMap_injective _ _
  -- That preimage is the set of non-zero-divisors of `MvPolynomial σ R`.
  have hEq : (nonZeroDivisors (MvPolynomial σ (FractionRing R))).comap
        (algebraMap (MvPolynomial σ R) (MvPolynomial σ (FractionRing R))) =
      nonZeroDivisors (MvPolynomial σ R) := by
    ext x
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact ⟨fun h hx => h (by rw [hx, map_zero]),
      fun hx h => hx (hinj (by rw [h, map_zero]))⟩
  haveI hQR : IsLocalization ((nonZeroDivisors (MvPolynomial σ (FractionRing R))).comap
        (algebraMap (MvPolynomial σ R) (MvPolynomial σ (FractionRing R))))
      (FractionRing (MvPolynomial σ R)) := by
    rw [hEq]; infer_instance
  -- Compare the two localizations of `MvPolynomial σ R`, then forget the scalar structure down
  -- to `R` and to `𝕜`.
  exact ⟨((IsLocalization.algEquiv ((nonZeroDivisors (MvPolynomial σ (FractionRing R))).comap
      (algebraMap (MvPolynomial σ R) (MvPolynomial σ (FractionRing R))))
      (FractionRing (MvPolynomial σ (FractionRing R)))
      (FractionRing (MvPolynomial σ R))).restrictScalars R).restrictScalars 𝕜⟩

/-- **Iterated rational function fields.**  `F(x₁,…,x_{a+b})`, i.e. the fraction field of
`MvPolynomial (Fin (a+b)) F`, is the rational function field in `a` variables over the rational
function field in `b` variables over `F`.

Route: `FractionRing (MvPolynomial (Fin (a+b)) F) ≅ FractionRing (MvPolynomial (Fin a) (MvPolynomial (Fin b) F))`
(`MvPolynomial.sumAlgEquiv` with `finSumFinEquiv`, then `IsFractionRing.algEquivOfAlgEquiv`), and
then pass to the fraction field of `MvPolynomial (Fin b) F` -- i.e. the statement of the sibling
file `Submission/Work/MotV5/fractionRing_mvPoly_fractionRing.lean`; reprove that special case
locally if you prefer not to depend on it. -/
theorem fractionRing_mvPoly_fin_add {𝕜 F : Type} [Field 𝕜] [Field F] [Algebra 𝕜 F]
    (a b : ℕ) :
    Nonempty (FractionRing (MvPolynomial (Fin (a + b)) F) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin a) (FractionRing (MvPolynomial (Fin b) F)))) := by
  -- First rewrite `F[x₀,…,x_{a+b-1}]` as `F[x₀,…,x_{b-1}][y₀,…,y_{a-1}]`.
  have e : MvPolynomial (Fin (a + b)) F ≃ₐ[𝕜]
      MvPolynomial (Fin a) (MvPolynomial (Fin b) F) :=
    ((MvPolynomial.renameEquiv F (finSumFinEquiv (m := a) (n := b)).symm).trans
      (MvPolynomial.sumAlgEquiv F (Fin a) (Fin b))).restrictScalars 𝕜
  have h₁ : Nonempty (FractionRing (MvPolynomial (Fin (a + b)) F) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin a) (MvPolynomial (Fin b) F))) :=
    ⟨IsFractionRing.algEquivOfAlgEquiv e⟩
  -- Then replace the coefficient ring `F[x₀,…,x_{b-1}]` by its fraction field.
  have h₂ : Nonempty (FractionRing (MvPolynomial (Fin a) (FractionRing (MvPolynomial (Fin b) F)))
      ≃ₐ[𝕜] FractionRing (MvPolynomial (Fin a) (MvPolynomial (Fin b) F))) :=
    nonempty_fractionRing_mvPolynomial_fractionRing (R := MvPolynomial (Fin b) F) (Fin a)
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂.symm⟩

end Work.MotV5
