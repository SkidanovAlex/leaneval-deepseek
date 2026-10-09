import Mathlib
import Submission.NK.RamificationDeep.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RamificationDeep

/-- The residue field of a discrete valuation ring is a field; hence its unit group has one
element fewer than the residue field itself: `#κˣ = #κ - 1`.

(`Nat.card_units` is unconditional for a `GroupWithZero`, and `#κ` is substituted by the
hypothesis `hq`; the DVR hypothesis only serves to guarantee that `𝔪_A` is the maximal ideal,
so that `A ⧸ 𝔪_A` really is a field, i.e. a `GroupWithZero`.) -/
theorem natCard_units_residueField {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A] {p f : ℕ}
    (hq : Nat.card (A ⧸ IsLocalRing.maximalIdeal A) = p ^ f) :
    Nat.card ((A ⧸ IsLocalRing.maximalIdeal A)ˣ) = p ^ f - 1 := by
  refine (@Nat.card_units (A ⧸ IsLocalRing.maximalIdeal A)
    (Ideal.Quotient.groupWithZero (IsLocalRing.maximalIdeal A))).trans ?_
  rw [hq]

end NK.RamificationDeep
