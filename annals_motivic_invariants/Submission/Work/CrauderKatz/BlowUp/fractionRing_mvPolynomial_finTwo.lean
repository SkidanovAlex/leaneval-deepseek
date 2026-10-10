import Mathlib
import Submission.Work.CrauderKatz.isFractionRing_polynomial_ratFunc
import Submission.Work.CrauderKatz.ratFunc_equiv_fractionRing_polynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.CrauderKatz.BlowUp

open Polynomial

/-- The fraction field of the polynomial ring `𝕜[t,z]` in two variables is the iterated rational
function field `𝕜(t)(z) = RatFunc (RatFunc 𝕜)`.

Route: `MvPolynomial.finSuccEquiv 𝕜 1 : MvPolynomial (Fin 2) 𝕜 ≃ₐ[𝕜] Polynomial (MvPolynomial (Fin 1) 𝕜)`
(or `MvPolynomial.finSuccEquiv 𝕜 2` twice, with `MvPolynomial.uniqueAlgEquiv` for `Fin 0`) and
`MvPolynomial.uniqueAlgEquiv`/`MvPolynomial.pUnitAlgEquiv` for the one-variable case give
`MvPolynomial (Fin 2) 𝕜 ≃ₐ[𝕜] Polynomial (Polynomial 𝕜)`; then either
`Work.CrauderKatz.ratFunc_equiv_fractionRing_polynomial (Polynomial 𝕜) (RatFunc 𝕜)`
(note `IsFractionRing (Polynomial 𝕜) (RatFunc 𝕜)` holds) or
`Work.CrauderKatz.isFractionRing_polynomial_ratFunc` gives that `RatFunc (RatFunc 𝕜)` is a fraction
ring of `Polynomial (Polynomial 𝕜)`, and two fraction rings of the same domain are isomorphic
(`IsLocalization.algEquiv`).  Transport along the algebra equivalence of the polynomial rings
(`IsFractionRing.isFractionRing_iff_of_base_ringEquiv`, or `Ideal`-free localizations), and check the
`𝕜`-algebra structures agree (they are the composites of `algebraMap 𝕜` with the polynomial/localization
structure maps). -/
theorem fractionRing_mvPolynomial_finTwo (𝕜 : Type) [Field 𝕜] :
    Nonempty (FractionRing (MvPolynomial (Fin 2) 𝕜) ≃ₐ[𝕜] RatFunc (RatFunc 𝕜)) := by
  -- `RatFunc (RatFunc 𝕜) = RatFunc K` with `K = RatFunc 𝕜` is a fraction ring of
  -- `K[z] = RatFunc 𝕜[z]`.  To view it as a fraction ring of `𝕜[t][z]` we use the `𝕜[t][z]`-algebra
  -- structure given by the composite of coefficient extension `𝕜[t][z] → K[z]` and the
  -- field-of-fractions structure map `K[z] → K(z)`.
  letI : Algebra (Polynomial (Polynomial 𝕜)) (RatFunc (RatFunc 𝕜)) :=
    (RingHom.toAlgebra
      ((algebraMap (Polynomial (RatFunc 𝕜)) (RatFunc (RatFunc 𝕜))).comp
        (Polynomial.mapRingHom (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)))))
  -- `Work.CrauderKatz.isFractionRing_polynomial_ratFunc` applied to the domain `A = 𝕜[t]` with
  -- fraction field `K = 𝕜(t)` shows that `K(z) = RatFunc (RatFunc 𝕜)` is a fraction ring of
  -- `A[z] = 𝕜[t][z]` (the algebra structure is the one just fixed, so the hypothesis is `rfl`).
  haveI : IsFractionRing (Polynomial (Polynomial 𝕜)) (RatFunc (RatFunc 𝕜)) :=
    Work.CrauderKatz.isFractionRing_polynomial_ratFunc (A := Polynomial 𝕜) (K := RatFunc 𝕜)
      (fun _ => rfl)
  -- The base `𝕜`-algebra structures agree, i.e. the two algebra maps `𝕜 → 𝕜(t)(z)` coincide;
  -- this is exactly the scalar-tower condition needed to apply `IsFractionRing.algEquivOfAlgEquiv`.
  haveI : IsScalarTower 𝕜 (Polynomial (Polynomial 𝕜)) (RatFunc (RatFunc 𝕜)) := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    show algebraMap 𝕜 (RatFunc (RatFunc 𝕜)) c =
      ((algebraMap (Polynomial (RatFunc 𝕜)) (RatFunc (RatFunc 𝕜))).comp
        (Polynomial.mapRingHom (algebraMap (Polynomial 𝕜) (RatFunc 𝕜))))
        (algebraMap 𝕜 (Polynomial (Polynomial 𝕜)) c)
    rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.algebraMap_apply,
      Polynomial.map_C, ← IsScalarTower.algebraMap_apply 𝕜 (Polynomial 𝕜) (RatFunc 𝕜) c,
      IsScalarTower.algebraMap_apply 𝕜 (Polynomial (RatFunc 𝕜)) (RatFunc (RatFunc 𝕜)) c,
      Polynomial.algebraMap_apply]
  -- Transport along `Polynomial (Polynomial 𝕜) ≃ₐ[𝕜] MvPolynomial (Fin 2) 𝕜`.
  exact ⟨IsFractionRing.algEquivOfAlgEquiv (Polynomial.Bivariate.equivMvPolynomial 𝕜).symm⟩

end Work.CrauderKatz.BlowUp
