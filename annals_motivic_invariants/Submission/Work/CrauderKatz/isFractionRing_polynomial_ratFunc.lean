import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.CrauderKatz

open Polynomial

/-- If `K` is a fraction field of the domain `A`, then the composite

`A[X] --Polynomial.map (algebraMap A K)--> K[X] --algebraMap--> RatFunc K`

is a localization of `A[X]` at its nonzerodivisors, i.e. the underlying

`Submonoid.IsLocalizationMap` statement.  This is the "concrete" form of the statement that
`RatFunc K` is a fraction ring of `A[X]`, phrased purely in terms of the map (and therefore
independent of which `Algebra (Polynomial A) (RatFunc K)` structure is around). -/
private theorem isLocalizationMap_composite {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] :
    (nonZeroDivisors (Polynomial A)).IsLocalizationMap
      (fun p : Polynomial A =>
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.map (algebraMap A K) p)) := by
  -- `K` is a fraction ring of `A`, hence `A` is a domain.
  haveI : IsDomain A := Function.Injective.isDomain (algebraMap A K) (IsFractionRing.injective A K)
  -- `A[X]` is the `A`-algebra whose structure map is `Polynomial.map (algebraMap A K)`.
  letI : Algebra (Polynomial A) (Polynomial K) := Polynomial.algebra A K
  -- `K[X]` is the localization of `A[X]` at the images of the nonzerodivisors of `A`.
  haveI hloc : IsLocalization ((nonZeroDivisors A).map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors A) K
  -- The pullback of the nonzerodivisors of `K[X]` is exactly the set of nonzerodivisors of
  -- `A[X]`: both are the nonzero polynomials and `Polynomial.map` is injective.
  have hcomap : Submonoid.comap (algebraMap (Polynomial A) (Polynomial K))
      (nonZeroDivisors (Polynomial K)) = nonZeroDivisors (Polynomial A) := by
    ext f
    simp only [Submonoid.mem_comap]
    rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    rw [Polynomial.algebraMap_def, Polynomial.coe_mapRingHom]
    exact Polynomial.map_ne_zero_iff (IsFractionRing.injective A K)
  haveI hST : IsScalarTower (Polynomial A) (Polynomial K) (RatFunc K) := inferInstance
  -- `RatFunc K = Frac K[X]` is the localization of `K[X]` at its nonzerodivisors, and every unit
  -- of `K[X]` is a nonzerodivisor, so the "localization of a localization" lemma identifies it
  -- with the localization of `A[X]` at the pullback submonoid computed above.
  have hloc2 : IsLocalization (nonZeroDivisors (Polynomial A)) (RatFunc K) := by
    have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
      ((nonZeroDivisors A).map Polynomial.C) (nonZeroDivisors (Polynomial K)) (RatFunc K)
      (fun x hx => hx.mem_nonZeroDivisors)
    rwa [hcomap] at h
  -- The structure map of this localization is precisely the composite appearing in the statement.
  have halg : ⇑(algebraMap (Polynomial A) (RatFunc K)) =
      (fun p : Polynomial A =>
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.map (algebraMap A K) p)) := by
    funext p
    rw [RatFunc.algebraMap_apply, Polynomial.algebraMap_def, Polynomial.coe_mapRingHom]
    simp
  exact halg ▸ hloc2.toIsLocalizationMap

theorem isFractionRing_polynomial_ratFunc {A K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Algebra (Polynomial A) (RatFunc K)] (hφ : ∀ p : Polynomial A, algebraMap (Polynomial A) (RatFunc K) p = algebraMap (Polynomial K) (RatFunc K) (Polynomial.map (algebraMap A K) p)) : IsFractionRing (Polynomial A) (RatFunc K) := by
  -- The map `algebraMap (Polynomial A) (RatFunc K)` of the given (arbitrary) algebra structure
  -- agrees, by `hφ`, with the composite map whose localization property was proved above.
  have hmap := isLocalizationMap_composite (A := A) (K := K)
  have heq : ⇑(algebraMap (Polynomial A) (RatFunc K)) =
      (fun p : Polynomial A =>
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.map (algebraMap A K) p)) :=
    funext hφ
  exact IsLocalization'.mk (heq ▸ hmap)

end Work.CrauderKatz
