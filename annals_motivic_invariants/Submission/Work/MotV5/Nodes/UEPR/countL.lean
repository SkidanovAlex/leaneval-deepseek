import Mathlib
import Submission.Work.MotV5.Nodes.UEPR.count

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.MotV5.Nodes.UEPR

/-
The fundamental identity of ramification theory, *at a fixed prime*: for `Ω/F` finite Galois,
`A = v.valuationSubring` a DVR of `F` (so `v` nontrivial), `B = integralClosure A Ω` and `P` a
prime of `B` above `m_A`,
`#(primes of B over m_A) * (e(P/m_A) * f(P/m_A)) = [Ω : F]`.

Because `Ω/F` is Galois, all the primes over `m_A` have the same `e` and `f`, so this is just
`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` rewritten with
`Ideal.ramificationIdxIn_eq_ramificationIdx` and `Ideal.inertiaDegIn_eq_inertiaDeg`, plus
`IsGalois.card_aut_eq_finrank`.

The instances needed (see `Submission/Work/MotR/R4/invariance_of_totallyRamified_place.lean`,
step 8, for the same setup with a DVR in place of `↥A`): `IsDedekindDomain ↥A`,
`IsIntegralClosure ↥B ↥A Ω`, `IsFractionRing ↥B Ω`, `IsDedekindDomain ↥B`,
`Module.Finite ↥A ↥B`, `Module.Flat ↥A ↥B`, `Algebra.IsAlgebraic F Ω`,
`MulSemiringAction Gal(Ω/F) ↥B` (`IsIntegralClosure.MulSemiringAction ↥A F Ω ↥B`) and
`IsGaloisGroup Gal(Ω/F) ↥A ↥B` (`IsGaloisGroup.of_isFractionRing`).
A sibling lemma `Work.MotV5.Nodes.UEPR.count` proves the `ramificationIdxIn`/`inertiaDegIn` form.
-/
theorem countL {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω] (v : Valuation F (WithZero (Multiplicative ℤ))) (hv : v.IsNontrivial) (P : Ideal ↥(integralClosure ↥(v.valuationSubring) Ω)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ↥(v.valuationSubring))] : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver ↥(integralClosure ↥(v.valuationSubring) Ω)).ncard * (P.ramificationIdx ↥(v.valuationSubring) * P.inertiaDeg ↥(v.valuationSubring)) = Module.finrank F Ω := by
  haveI hv' : v.IsNontrivial := hv
  -- The base ring `A = v.valuationSubring` is a discrete valuation ring.
  haveI hDVR : IsDiscreteValuationRing ↥(v.valuationSubring) := inferInstance
  haveI hDedA : IsDedekindDomain ↥(v.valuationSubring) := inferInstance
  haveI hICL : IsIntegrallyClosed ↥(v.valuationSubring) := inferInstance
  haveI hFracA : IsFractionRing ↥(v.valuationSubring) F := inferInstance
  haveI hST1 : IsScalarTower ↥(v.valuationSubring) F Ω := inferInstance
  -- The integral closure `B = integralClosure A Ω`.
  haveI hDomB : IsDomain ↥(integralClosure ↥(v.valuationSubring) Ω) := inferInstance
  haveI hIC : IsIntegralClosure ↥(integralClosure ↥(v.valuationSubring) Ω)
    ↥(v.valuationSubring) Ω := inferInstance
  haveI hFracB : IsFractionRing ↥(integralClosure ↥(v.valuationSubring) Ω) Ω :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥(v.valuationSubring) F Ω
      ↥(integralClosure ↥(v.valuationSubring) Ω)
  haveI hFin : Module.Finite ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    IsIntegralClosure.finite ↥(v.valuationSubring) F Ω ↥(integralClosure ↥(v.valuationSubring) Ω)
  haveI hIntB : Algebra.IsIntegral ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    ⟨fun x => IsIntegralClosure.isIntegral ↥(v.valuationSubring) Ω x⟩
  -- The Galois action on the integral closure and the `IsGaloisGroup` structure.
  letI hAct : MulSemiringAction (Ω ≃ₐ[F] Ω) ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    IsIntegralClosure.MulSemiringAction ↥(v.valuationSubring) F Ω
      ↥(integralClosure ↥(v.valuationSubring) Ω)
  haveI hGal : IsGaloisGroup (Ω ≃ₐ[F] Ω) ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    IsGaloisGroup.of_isFractionRing (Ω ≃ₐ[F] Ω) ↥(v.valuationSubring) _ F Ω
  -- The sibling lemma gives the `ramificationIdxIn`/`inertiaDegIn` form; because `Ω/F` is Galois
  -- these agree with the ramification index and inertia degree of any prime above `m_A`.
  rw [← count v hv,
    Ideal.ramificationIdxIn_eq_ramificationIdx (IsLocalRing.maximalIdeal ↥(v.valuationSubring)) P
      (Ω ≃ₐ[F] Ω),
    Ideal.inertiaDegIn_eq_inertiaDeg (IsLocalRing.maximalIdeal ↥(v.valuationSubring)) P
      (Ω ≃ₐ[F] Ω)]

end Work.MotV5.Nodes.UEPR
