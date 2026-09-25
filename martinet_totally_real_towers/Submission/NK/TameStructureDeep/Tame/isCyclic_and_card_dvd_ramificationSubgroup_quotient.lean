import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.RamificationDeep.UnitMap
import Submission.NK.RamificationDeep.WildInertiaUnconditional
import Submission.NK.RamificationDeep.isCyclic_quotient_ramificationSubgroup
import Submission.NK.RamificationDeep.natCard_units_residueField
import Submission.NK.RamificationDeep.uniformizerData_of_isGalois

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Tame

/-- **The tame inertia quotient `G_0/G_1` is cyclic of order dividing `#(A/𝔪_A) - 1`.**

For a Galois-stable discrete valuation ring `A` of a finite Galois extension `M/κ` with finite
residue field, the quotient of the inertia subgroup `G_0 = ramificationSubgroup A 0` by the wild
inertia `G_1 = ramificationSubgroup A 1` is cyclic, and its order divides
`#(A/𝔪_A) - 1`.  Indeed the coordinate map `σ ↦ σ(π)/π` embeds `G_0/G_1` into the unit group
`(A/𝔪_A)^×` (`unitHom_ker`), and the unit group of a finite field is cyclic. -/
theorem isCyclic_and_card_dvd_ramificationSubgroup_quotient
    {κ M : Type*} [Field κ] [Field M] [Algebra κ M] [FiniteDimensional κ M] [IsGalois κ M]
    (A : ValuationSubring M) [IsDiscreteValuationRing A] [HenselianLocalRing A]
    (hdec : A.decompositionSubgroup κ = ⊤) [Finite (IsLocalRing.ResidueField A)] :
    IsCyclic ((NK.Ramification.ramificationSubgroup (K := κ) A 0) ⧸
        (NK.Ramification.ramificationSubgroup (K := κ) A 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := κ) A 0)) ∧
      Nat.card ((NK.Ramification.ramificationSubgroup (K := κ) A 0) ⧸
        (NK.Ramification.ramificationSubgroup (K := κ) A 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := κ) A 0)) ∣
        Nat.card (IsLocalRing.ResidueField A) - 1 := by
  haveI : PerfectField (IsLocalRing.ResidueField A) := inferInstance
  obtain ⟨π, E, D⟩ :=
    NK.RamificationDeep.uniformizerData_of_isGalois (K := κ) (L := M) A hdec
  haveI hcycRes : IsCyclic (IsLocalRing.ResidueField A)ˣ := inferInstance
  have hcyc : IsCyclic ((A ⧸ IsLocalRing.maximalIdeal A)ˣ) := hcycRes
  refine ⟨?_, ?_⟩
  · exact NK.RamificationDeep.isCyclic_quotient_ramificationSubgroup
      (K := κ) A π E D hcyc
  · have h := NK.RamificationDeep.natCard_quotient_zero_dvd_units (K := κ) D
    rw [← Nat.card_units (IsLocalRing.ResidueField A)]
    exact h

end NK.TameStructureDeep.Tame
