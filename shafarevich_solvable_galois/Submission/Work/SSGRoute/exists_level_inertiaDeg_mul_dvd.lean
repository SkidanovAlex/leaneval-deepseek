import Mathlib
import Submission.Work.SSGRoute.inertiaAtLevelDefs
import Submission.Work.LocalFields.exists_monic_irreducible_reduction
import Submission.Work.SSGRoute.level_residueDeg_dvd_general
import Submission.NK.FrobeniusBridge.Descent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Increasing the inertia degree at a finite place by passing to a larger normal level

For a finite place `A` of an algebraic closure `Ω` of a number field `k`, a finite normal number
field `M ⊆ Ω` and any `N ≠ 0`, we produce a finite normal number field `M' ⊆ Ω` with `M ≤ M'` such
that the residue degree (`Ideal.inertiaDeg`) of the prime of `𝓞 M'` below `A` over `𝓞 k` is
divisible by `N` times the residue degree of the prime of `𝓞 M` below `A`.

The argument has two ingredients.

* **Residue degrees can be made divisible by any prescribed `d`**:
  `Work.SSGRoute.level_residueDeg_dvd_general` (proved in
  `Submission/Work/SSGRoute/level_residueDeg_dvd_general.lean`) gives, for every `d > 0`, a finite
  normal number field `L ⊆ Ω` with `d ∣ inertiaDeg(levelPrime L)`; this is the cyclotomic
  construction `L = k⟮ζ_m⟯`, `m = q ^ d - 1` (`q` the size of the residue field of `k` at the prime
  below `A`).

* **Inertia degrees multiply along a tower of levels**: for `L ≤ M'` finite normal levels the prime
  of `𝓞 L` below `A` is the contraction of the prime of `𝓞 M'` below `A`
  (`NK.FrobeniusBridge.primeOfLevel_under`), so `Ideal.inertiaDeg` is multiplicative in towers and
  `inertiaDeg(levelPrime L) ∣ inertiaDeg(levelPrime M')` (`Ideal.inertiaDeg_below_dvd`); this is
  `levelPrime_inertiaDeg_dvd_of_le` below.

The proof of the theorem is then: apply the first ingredient with `d := N * inertiaDeg(levelPrime M)`
to get `L`, and take `M' := M ⊔ L`, which is finite, normal and a number field over `k` (compositum
of two such), contains `M`, and contains `L` — so that
`N * inertiaDeg(levelPrime M) ∣ inertiaDeg(levelPrime L) ∣ inertiaDeg(levelPrime M')`.
-/

open SSGRoute
open scoped NumberField

namespace Work.SSGRoute

set_option linter.style.haveILetI false

/-- **The inertia degree at a finite place is monotone in the level**: for finite normal levels
`L ≤ M'` of `Ω`, the residue degree of the prime of `𝓞 L` below `A` over `𝓞 k` divides that of the
prime of `𝓞 M'` below `A`.

`levelPrime A M'` lies over `levelPrime A L` because the prime of a level below a place is the
contraction of the prime of any larger level (`NK.FrobeniusBridge.primeOfLevel_under`), and
inertia degrees are multiplicative in towers (`Ideal.inertiaDeg_below_dvd`).  The algebra structure
`𝓞 ↥L → 𝓞 ↥M'` is the one induced by the field inclusion `L ≤ M'`. -/
theorem levelPrime_inertiaDeg_dvd_of_le {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    {L M' : IntermediateField k Ω} [FiniteDimensional k L] [Normal k L] [NumberField ↥L]
    [FiniteDimensional k M'] [Normal k M'] [NumberField ↥M'] (hLM' : L ≤ M')
    [Algebra ↥L ↥M'] [IsScalarTower k ↥L ↥M'] [IsScalarTower ↥L ↥M' Ω] :
    (levelPrime k Ω A hA L).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) ∣
      (levelPrime k Ω A hA M').asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
  haveI : IsSepClosure k Ω := inferInstance
  -- the prime of `𝓞 L` is the contraction of the prime of `𝓞 M'`
  have hunder : levelPrime k Ω A hA L =
      (levelPrime k Ω A hA M').under (NumberField.RingOfIntegers ↥L) :=
    NK.FrobeniusBridge.primeOfLevel_under (K := k) (K' := Ω) hLM'
      (⟨A, hA⟩ : NK.FrobeniusBridge.FinitePlaceOf k Ω)
  haveI hlies : (levelPrime k Ω A hA M').asIdeal.LiesOver (levelPrime k Ω A hA L).asIdeal := by
    refine Ideal.LiesOver.mk ?_
    rw [hunder, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
  exact Ideal.inertiaDeg_below_dvd (levelPrime k Ω A hA L).asIdeal
    (levelPrime k Ω A hA M').asIdeal

theorem exists_level_inertiaDeg_mul_dvd
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M]
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (M' : IntermediateField k Ω) (_ : FiniteDimensional k M') (_ : Normal k M')
      (_ : NumberField ↥M') (_ : M ≤ M'),
      N * (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) ∣
        (Work.SSGRoute.levelPrime k Ω A hA M').asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
  -- the residue degree of the given level is positive, so `N * f_M` is a positive target
  have hfMpos : 0 < (levelPrime k Ω A hA M).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
    Ideal.inertiaDeg_pos _ _
  have hdpos : 0 < N * (levelPrime k Ω A hA M).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) :=
    Nat.mul_pos (Nat.pos_of_ne_zero hN) hfMpos
  -- a finite normal level whose residue degree is a multiple of `N * f_M`
  obtain ⟨L, hLfin, hLnorm, hLnf, hdvd⟩ :=
    level_residueDeg_dvd_general k Ω A hA
      (N * (levelPrime k Ω A hA M).asIdeal.inertiaDeg (NumberField.RingOfIntegers k)) hdpos
  letI : FiniteDimensional k L := hLfin
  letI : Normal k L := hLnorm
  letI : NumberField ↥L := hLnf
  -- the compositum `M ⊔ L`, which is again finite, normal and a number field over `k`
  let M' : IntermediateField k Ω := M ⊔ L
  have hMle : M ≤ M' := le_sup_left
  have hLle : L ≤ M' := le_sup_right
  letI : Algebra ↥L ↥M' := (Subsemiring.inclusion hLle).toAlgebra
  haveI hST1 : IsScalarTower k ↥L ↥M' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hST2 : IsScalarTower ↥L ↥M' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hsupfin : FiniteDimensional k M' := inferInstance
  haveI hsupnorm : Normal k M' := inferInstance
  haveI hsupnf : NumberField ↥M' := NumberField.of_module_finite k ↥M'
  refine ⟨M', hsupfin, hsupnorm, hsupnf, hMle, ?_⟩
  exact dvd_trans hdvd (levelPrime_inertiaDeg_dvd_of_le A hA hLle)

end Work.SSGRoute
