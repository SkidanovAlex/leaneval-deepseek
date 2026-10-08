import Mathlib
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

/-- **Z2 (blueprint §ZASS), fiber count.** The elements of `B = G_∞` fixing a point `x` are
exactly the two-point stabilizer `G_{∞x} = pairStab G inf x`; removing the identity leaves
`|G_{∞x}| - 1` of them.

Stated with the order of `G_{∞x}` as a parameter `m`, so that the caller may supply it from
`Work.ZASS.natCard_pairStab`. -/
theorem ncard_fiber {G X : Type} [Group G] [MulAction G X] {inf x : X} {m : ℕ}
    (hm : Nat.card (Work.Zassenhaus.pairStab G inf x) = m) :
    ({g : G | g ∈ Work.Zassenhaus.borel G inf ∧ g ≠ 1 ∧ g • x = x} : Set G).ncard
      = m - 1 := by
  have hset : {g : G | g ∈ Work.Zassenhaus.borel G inf ∧ g ≠ 1 ∧ g • x = x}
      = (Work.Zassenhaus.pairStab G inf x : Set G) \ {1} := by
    ext g
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq, SetLike.mem_coe,
      Work.Zassenhaus.mem_borel_iff, Work.Zassenhaus.mem_pairStab_iff]
    tauto
  have hcoe : Nat.card (Work.Zassenhaus.pairStab G inf x)
      = (Work.Zassenhaus.pairStab G inf x : Set G).ncard := Nat.card_coe_set_eq _
  rw [hset, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), ← hcoe, hm]

end Work.ZASS
