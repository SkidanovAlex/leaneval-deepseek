import Mathlib
import Submission.Work.GLUE.Defs

namespace Work.GLUE

/-- `Work.GW2.IsHallIn I K` (a relative Hall subgroup of `K` in the ambient `G`, phrased as
`I ≤ K` together with coprimality of `|I|` and the relative index `[K : I]`) agrees with the
Isaacs notion `IsHallSubgroup π H` for `H = I.subgroupOf K` and `π = primesOf I`, the set of
primes dividing `|I|`: the "π-group" half of `IsHallSubgroup` is automatic because
`|I.subgroupOf K| = |I|`, and the "π'-index" half is exactly the coprimality condition, since
`I.relIndex K = (I.subgroupOf K).index`. -/
theorem isHallIn_iff_isHallSubgroup {G : Type*} [Group G] [Finite G] {I K : Subgroup G}
    (h : I ≤ K) :
    Work.GW2.IsHallIn I K ↔
      OddOrder.Isaacs.Ch03.IsHallSubgroup (Work.GW2.primesOf I) (I.subgroupOf K) := by
  have hcard : Nat.card (I.subgroupOf K) = Nat.card I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have hI : Nat.card I ≠ 0 := (Nat.card_pos).ne'
  have hK : (I.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [Work.GW2.IsHallIn, Work.GW2.primesOf, OddOrder.Isaacs.Ch03.IsHallSubgroup, hcard]
  constructor
  · rintro ⟨-, hc⟩
    refine ⟨fun p hp => hp, ?_⟩
    intro p hp hpa
    exact (Finset.disjoint_left.mp hc.symm.disjoint_primeFactors hp) hpa
  · rintro ⟨-, hnc⟩
    refine ⟨h, ?_⟩
    exact ((Nat.disjoint_primeFactors hK hI).mp (Finset.disjoint_left.mpr hnc)).symm

end Work.GLUE
