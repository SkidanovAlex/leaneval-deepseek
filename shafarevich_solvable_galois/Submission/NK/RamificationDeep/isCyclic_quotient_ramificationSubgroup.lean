import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.NK.RamificationDeep.WildInertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.RamificationDeep

open scoped Pointwise

/-- **`G_0/G_1` is cyclic when the residue field units are.**  The coordinate map
`σ ↦ 1 + b_σ = σ(π)/π` of `NK.RamificationDeep.unitHom` is a homomorphism
`G_0 →* (A/𝔪_A)^×` with kernel exactly `G_1` (`NK.RamificationDeep.unitHom_ker`), so
`G_0/G_1` embeds into the (by hypothesis cyclic) group `(A/𝔪_A)^×`; a subgroup of a cyclic group
is cyclic. -/
theorem isCyclic_quotient_ramificationSubgroup {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A] (π : A) (E : IntermediateField K L)
    (D : NK.RamificationDeep.UniformizerData (K := K) A π E)
    [Finite ↥(A.decompositionSubgroup K)]
    (hcyc : IsCyclic ((A ⧸ IsLocalRing.maximalIdeal A)ˣ)) :
    IsCyclic (↥(NK.Ramification.ramificationSubgroup (K := K) A 0) ⧸
      (NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := K) A 0)) := by
  haveI : IsCyclic ((A ⧸ IsLocalRing.maximalIdeal A)ˣ) := hcyc
  have hker := unitHom_ker (K := K) D
  have e := QuotientGroup.quotientMulEquivOfEq hker.symm
  exact isCyclic_of_injective (MonoidHom.comp (QuotientGroup.kerLift (unitHom (K := K) D))
      e.toMonoidHom)
    ((QuotientGroup.kerLift_injective (unitHom (K := K) D)).comp e.injective)

end NK.RamificationDeep
