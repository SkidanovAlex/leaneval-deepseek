import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.CrauderKatz

/-- If `K` is a fraction ring of the ring `A` (so `A` is a domain and `K` is its fraction field),
then the rational function field `K(t)` is the fraction ring of `A[t]`: the two localizations
`RatFunc K` (= fraction field of `K[t]`) and `FractionRing A[t]` of `A[t]` coincide. -/
theorem ratFunc_equiv_fractionRing_polynomial (A K : Type) [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] :
    Nonempty (RatFunc K ≃+* FractionRing (Polynomial A)) := by
  -- Since `K` is a fraction ring of `A` and `K` is a field, `A` is a domain.
  haveI : IsDomain A :=
    Function.Injective.isDomain (algebraMap A K) (IsFractionRing.injective A K)
  -- `A[X]` is the `A`-algebra whose structure map is `Polynomial.map (algebraMap A K)`;
  -- this is Mathlib's (non-global) `Polynomial.algebra` instance.
  letI : Algebra (Polynomial A) (Polynomial K) := Polynomial.algebra A K
  -- `K[X]` is the localization of `A[X]` at the (images of the) nonzerodivisors of `A`.
  haveI hloc : IsLocalization ((nonZeroDivisors A).map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors A) K
  -- The pullback of the nonzerodivisors of `K[X]` along `A[X] → K[X]` is exactly the set of
  -- nonzerodivisors of `A[X]`: both are the nonzero polynomials, and `Polynomial.map` is injective.
  have hcomap : Submonoid.comap (algebraMap (Polynomial A) (Polynomial K))
      (nonZeroDivisors (Polynomial K)) = nonZeroDivisors (Polynomial A) := by
    ext f
    simp only [Submonoid.mem_comap]
    rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    rw [Polynomial.algebraMap_def, Polynomial.coe_mapRingHom]
    exact Polynomial.map_ne_zero_iff (IsFractionRing.injective A K)
  -- `Frac K[X]` is the localization of `K[X]` at its nonzerodivisors, and every unit of `K[X]`
  -- is a nonzerodivisor; the "localization of a localization" lemma identifies it with the
  -- localization of `A[X]` at the pullback submonoid computed above.
  have hT : IsLocalization (Submonoid.comap (algebraMap (Polynomial A) (Polynomial K))
      (nonZeroDivisors (Polynomial K))) (FractionRing (Polynomial K)) :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      ((nonZeroDivisors A).map Polynomial.C) (nonZeroDivisors (Polynomial K))
      (FractionRing (Polynomial K)) (fun x hx => hx.mem_nonZeroDivisors)
  -- Hence `Frac K[X]` is a fraction ring of `A[X]`, so it is isomorphic (as an `A[X]`-algebra)
  -- to `FractionRing A[X]`; composing with `RatFunc K ≃+* FractionRing K[X]` gives the claim.
  haveI : IsLocalization (nonZeroDivisors (Polynomial A)) (FractionRing (Polynomial K)) :=
    hcomap ▸ hT
  exact ⟨(RatFunc.toFractionRingRingEquiv K).trans
    (IsLocalization.algEquiv (nonZeroDivisors (Polynomial A)) (FractionRing (Polynomial K))
      (FractionRing (Polynomial A))).toRingEquiv⟩

end Work.CrauderKatz
