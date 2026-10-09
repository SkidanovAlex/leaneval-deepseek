import Mathlib
import Submission.Work.SSGRoute.InfInertiaClosureDefs
import Submission.Work.SSGRoute.levelIndex
import Submission.Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank
import Submission.NK.ResidueFrob.primeOfLevel_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped Pointwise NumberField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The index of the level inertia in the level decomposition group is the inertia degree.** -/
theorem levelInertia_index_eq_inertiaDeg (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (M : IntermediateField k Ω) [FiniteDimensional k M]
    [Normal k M] [NumberField ↥M] :
    ((Work.SSGRoute.levelInertiaAt k Ω A hA M).subgroupOf
        (Work.SSGRoute.levelDecompAt k Ω A hA M)).index =
      (Work.SSGRoute.levelPrimeAt k Ω A hA M).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers k) := by
  haveI hsep : IsSepClosure k Ω := inferInstance
  haveI hgal : IsGalois k ↥M :=
    isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  haveI hGal : IsGaloisGroup (↥M ≃ₐ[k] ↥M) (𝓞 k) (𝓞 M) := inferInstance
  haveI hlie : (levelPrimeAt k Ω A hA M).asIdeal.LiesOver
      (Submission.NeukirchUchida.primeOf A hA).asIdeal :=
    NK.ResidueFrob.primeOfLevel_liesOver (K := k) (K' := Ω) ⟨A, hA⟩ M
  haveI hperf : PerfectField (Submission.NeukirchUchida.primeOf A hA).asIdeal.ResidueField :=
    Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum _
  have hcard : Nat.card (levelDecompAt k Ω A hA M) =
      Nat.card (levelInertiaAt k Ω A hA M) *
      (levelPrimeAt k Ω A hA M).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
    Ideal.card_stabilizer_eq_card_inertia_mul_finrank
      (Submission.NeukirchUchida.primeOf A hA).asIdeal (levelPrimeAt k Ω A hA M).asIdeal
  have hc : Nat.card ((levelInertiaAt k Ω A hA M).subgroupOf (levelDecompAt k Ω A hA M)) =
      Nat.card (levelInertiaAt k Ω A hA M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Ideal.inertia_le_stabilizer (M := ↥M ≃ₐ[k] ↥M)
        (levelPrimeAt k Ω A hA M).asIdeal)).toEquiv
  have hmul : Nat.card ((levelInertiaAt k Ω A hA M).subgroupOf (levelDecompAt k Ω A hA M)) *
      ((levelInertiaAt k Ω A hA M).subgroupOf (levelDecompAt k Ω A hA M)).index =
      Nat.card (levelDecompAt k Ω A hA M) :=
    Subgroup.card_mul_index _
  have h1 : Nat.card ((levelInertiaAt k Ω A hA M).subgroupOf (levelDecompAt k Ω A hA M)) *
      ((levelInertiaAt k Ω A hA M).subgroupOf (levelDecompAt k Ω A hA M)).index =
      Nat.card ((levelInertiaAt k Ω A hA M).subgroupOf (levelDecompAt k Ω A hA M)) *
      (levelPrimeAt k Ω A hA M).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    rw [hmul, hc, hcard]
  haveI : Nonempty ↥((levelInertiaAt k Ω A hA M).subgroupOf
      (levelDecompAt k Ω A hA M)) := ⟨1⟩
  exact Nat.mul_left_cancel Nat.card_pos h1

end Work.SSGRoute
