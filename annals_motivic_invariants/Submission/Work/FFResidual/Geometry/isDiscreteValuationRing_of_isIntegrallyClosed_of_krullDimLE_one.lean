import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open IsLocalRing

namespace Work.FFResidual.Geometry

/-- A Noetherian local integrally closed domain of Krull dimension at most one which is not a
field is a discrete valuation ring. This is the local form of the fact that a
one-dimensional Noetherian integrally closed domain is a Dedekind domain whose local rings are
DVRs. -/
theorem isDiscreteValuationRing_of_isIntegrallyClosed_of_krullDimLE_one
    (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [Ring.KrullDimLE 1 R] [IsIntegrallyClosed R] (hnf : ¬ IsField R) :
    IsDiscreteValuationRing R := by
  -- The maximal ideal is nonzero since `R` is not a field.
  have hmax : maximalIdeal R ≠ ⊥ := fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  -- Every nonzero prime ideal is maximal (dimension ≤ 1) and hence equals the maximal ideal
  -- (locality).
  have huniq : ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = maximalIdeal R :=
    fun P hP hPp => IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)
  have hitem : IsIntegrallyClosed R ∧ ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = maximalIdeal R :=
    ⟨inferInstance, huniq⟩
  -- Use the TFAE characterisation of DVRs: integrally closed with a unique nonzero prime
  -- ideal implies principal ideal ring.
  have hpid : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 1).mp hitem
  exact { not_a_field' := hmax }

end Work.FFResidual.Geometry
