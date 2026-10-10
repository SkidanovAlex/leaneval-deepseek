import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.MotV5.Nodes.UEPR

/-- Torsion-freeness from injectivity of the structure map. -/
theorem noZeroSMulDivisors_of_algebraMap_injective {A B : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [NoZeroDivisors B] (h : Function.Injective (algebraMap A B)) :
    NoZeroSMulDivisors A B where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} hcx := by
    by_cases hc : c = 0
    · exact Or.inl hc
    · refine Or.inr ?_
      have h2 : algebraMap A B c * x = 0 := by rwa [Algebra.smul_def] at hcx
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (fun hh => hc (h (by rw [hh, map_zero])))
      · exact h3

/-
The fundamental identity of ramification theory for the Galois extension `Ω/F` at the (base)
discrete valuation ring `A = v.valuationSubring` of `F`: the number of primes of the integral
closure `B = integralClosure A Ω` above the maximal ideal `m_A`, times `e * f` (ramification index
times inertia degree, the same for all primes over `m_A` because `Ω/F` is Galois), equals
`[Ω : F] = Module.finrank F Ω`.

Route: `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` applied with
`G := Gal(Ω/F)`, `A := ↥(v.valuationSubring)`, `B := ↥(integralClosure ↥(v.valuationSubring) Ω)`,
combined with `IsGalois.card_aut_eq_finrank`.  The instances needed:
* `IsDedekindDomain ↥A` (from `v.IsNontrivial`: `↥A` is a DVR),
* `IsIntegralClosure ↥B ↥A Ω`, `IsFractionRing ↥B Ω`
  (`IsIntegralClosure.isFractionRing_of_finite_extension`), `IsDedekindDomain ↥B`
  (`IsIntegralClosure.isDedekindDomain`), `Module.Finite ↥A ↥B` (`IsIntegralClosure.finite`),
  `Module.Flat ↥A ↥B` (from torsion-freeness),
* the Galois group action `IsIntegralClosure.MulSemiringAction ↥A F Ω ↥B` and
  `IsGaloisGroup Gal(Ω/F) ↥A ↥B` (`IsGaloisGroup.of_isFractionRing` with
  `IsGaloisGroup.of_isGalois F Ω`).
The file `Submission/Work/MotR/R4/invariance_of_totallyRamified_place.lean` (step 8) sets up
exactly these instances for a DVR in place of `↥A` and can be copied.
-/
theorem count {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω] (v : Valuation F (WithZero (Multiplicative ℤ))) (hv : v.IsNontrivial) : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver ↥(integralClosure ↥(v.valuationSubring) Ω)).ncard * ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).ramificationIdxIn ↥(integralClosure ↥(v.valuationSubring) Ω) * (IsLocalRing.maximalIdeal ↥(v.valuationSubring)).inertiaDegIn ↥(integralClosure ↥(v.valuationSubring) Ω)) = Module.finrank F Ω := by
  haveI hv' : v.IsNontrivial := hv
  -- The base ring `A = v.valuationSubring` is a discrete valuation ring.
  haveI hDVR : IsDiscreteValuationRing ↥(v.valuationSubring) := inferInstance
  haveI hDedA : IsDedekindDomain ↥(v.valuationSubring) := inferInstance
  haveI hICL : IsIntegrallyClosed ↥(v.valuationSubring) := inferInstance
  haveI hNoeth : IsNoetherianRing ↥(v.valuationSubring) := inferInstance
  haveI hFracA : IsFractionRing ↥(v.valuationSubring) F := inferInstance
  haveI hST1 : IsScalarTower ↥(v.valuationSubring) F Ω := inferInstance
  -- The integral closure `B = integralClosure A Ω`.
  haveI hDomB : IsDomain ↥(integralClosure ↥(v.valuationSubring) Ω) := inferInstance
  haveI hIC : IsIntegralClosure ↥(integralClosure ↥(v.valuationSubring) Ω)
    ↥(v.valuationSubring) Ω := inferInstance
  haveI hFracB : IsFractionRing ↥(integralClosure ↥(v.valuationSubring) Ω) Ω :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥(v.valuationSubring) F Ω
      ↥(integralClosure ↥(v.valuationSubring) Ω)
  haveI hSep : Algebra.IsSeparable F Ω := inferInstance
  haveI hFin : Module.Finite ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    IsIntegralClosure.finite ↥(v.valuationSubring) F Ω ↥(integralClosure ↥(v.valuationSubring) Ω)
  haveI hIntB : Algebra.IsIntegral ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    ⟨fun x => IsIntegralClosure.isIntegral ↥(v.valuationSubring) Ω x⟩
  -- `B` is torsion-free over `A`, hence flat (Dedekind domain).
  have hinj : Function.Injective
      (algebraMap ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω)) := by
    intro a b h
    have h1 : algebraMap ↥(v.valuationSubring) Ω a = algebraMap ↥(v.valuationSubring) Ω b := by
      rw [IsScalarTower.algebraMap_apply ↥(v.valuationSubring)
            ↥(integralClosure ↥(v.valuationSubring) Ω) Ω,
          IsScalarTower.algebraMap_apply ↥(v.valuationSubring)
            ↥(integralClosure ↥(v.valuationSubring) Ω) Ω, h]
    rw [IsScalarTower.algebraMap_apply ↥(v.valuationSubring) F Ω,
        IsScalarTower.algebraMap_apply ↥(v.valuationSubring) F Ω] at h1
    exact IsFractionRing.injective ↥(v.valuationSubring) F ((algebraMap F Ω).injective h1)
  haveI hNZ : NoZeroSMulDivisors ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    noZeroSMulDivisors_of_algebraMap_injective hinj
  haveI hTF : Module.IsTorsionFree ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) := inferInstance
  haveI hFlat : Module.Flat ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) := inferInstance
  -- The Galois action on the integral closure and the `IsGaloisGroup` structure.
  letI hAct : MulSemiringAction (Ω ≃ₐ[F] Ω) ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    IsIntegralClosure.MulSemiringAction ↥(v.valuationSubring) F Ω
      ↥(integralClosure ↥(v.valuationSubring) Ω)
  haveI hGal : IsGaloisGroup (Ω ≃ₐ[F] Ω) ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    IsGaloisGroup.of_isFractionRing (Ω ≃ₐ[F] Ω) ↥(v.valuationSubring) _ F Ω
  -- The fundamental identity of ramification theory.
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (p := IsLocalRing.maximalIdeal ↥(v.valuationSubring))
    ↥(integralClosure ↥(v.valuationSubring) Ω) (Ω ≃ₐ[F] Ω)
  rw [IsGalois.card_aut_eq_finrank F Ω] at hfund
  exact hfund

end Work.MotV5.Nodes.UEPR
