import Mathlib.GroupTheory.GroupAction.Jordan

open MulAction

namespace Commons.GroupTheory.GroupAction

/-- A proper preprimitive subgroup of a finite symmetric group contains no transposition.
This is the contrapositive of the theorem of Jordan: a primitive subgroup that
contains a swap is the full permutation group. -/
theorem primitive_ne_top_no_isSwap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Subgroup (Equiv.Perm ι)} (hG : IsPreprimitive G ι) (hGne : G ≠ ⊤) :
    ¬ ∃ g : Equiv.Perm ι, g.IsSwap ∧ g ∈ G := by
  rintro ⟨g, hswap, hmem⟩
  exact hGne (Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hG g hswap hmem)

end Commons.GroupTheory.GroupAction