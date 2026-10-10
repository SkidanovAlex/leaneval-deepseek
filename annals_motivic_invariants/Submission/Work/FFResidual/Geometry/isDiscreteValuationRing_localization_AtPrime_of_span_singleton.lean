import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FFResidual.Geometry

-- Please declare this in namespace `Work.FFResidual.Geometry`.
-- Hints from reviewers: `haveI : IsDomain (Localization.AtPrime _)` comes from
-- `Localization.isDomain_of_local_atPrime`; use `Localization.AtPrime.map_eq_maximalIdeal` (note the
-- `←` orientation) with `Ideal.map_span` to get that the maximal ideal is `span {algebraMap x}`, hence
-- principal, hence `IsDiscreteValuationRing` via `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`
-- / `IsDiscreteValuationRing.TFAE` (the `List.TFAE.out` indices are 1-based there).
theorem isDiscreteValuationRing_localization_AtPrime_of_span_singleton
    {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] {x : A} (hx : x ≠ 0)
    [hp : (Ideal.span {x} : Ideal A).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {x} : Ideal A)) := by
  let R := Localization.AtPrime (Ideal.span {x} : Ideal A)
  haveI : IsDomain R := IsLocalization.isDomain_of_local_atPrime hp
  haveI : IsLocalRing R := Localization.AtPrime.isLocalRing (Ideal.span {x} : Ideal A)
  -- `algebraMap A R` is injective because `A` is a domain.
  have hinj : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R (M := (Ideal.span {x} : Ideal A).primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {x} : Ideal A))
  -- The maximal ideal of `R` is the image of `span {x}`, i.e. `span {algebraMap A R x}`.
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap A R x} := by
    have h1 : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {x} : Ideal A))
        = Ideal.span {algebraMap A (Localization.AtPrime (Ideal.span {x} : Ideal A)) x} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal (I := (Ideal.span {x} : Ideal A)),
        Ideal.map_span]
      simp
    exact h1
  have hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal := by
    rw [hmax]; infer_instance
  -- `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`: 5th condition ⇒ 1st condition.
  have hpid : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 5 1).mp hprincipal
  haveI := hpid
  refine IsDiscreteValuationRing.mk ?_
  rw [hmax]
  intro h
  exact hx (hinj (by rw [Ideal.span_singleton_eq_bot.mp h, map_zero]))

end Work.FFResidual.Geometry
