import Mathlib
import Submission.Work.Hering.InvSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.V

/-- If `V = Inv(G) ∪ {1}` has exactly `8` elements, then it contains a subgroup of `G` of order
`4`. Indeed `V` is a finite `2`-group (`Work.Hering.isPGroup_invSubgroup`), so Sylow's first
theorem in the form `Sylow.exists_subgroup_le_card_pow_prime_of_le_card` produces, inside `V`
and for every `n` with `2 ^ n ≤ |V|`, a subgroup of cardinality `2 ^ n`; taking `n = 2` and
transporting the resulting subgroup of `↥V` back to `G` along the injection `V ↪ G` gives a
subgroup of `G` of order `4` contained in `V`. -/
theorem exists_subgroup_card_four {G : Type*} [Group G] [Finite G] {hDT : DTInv G}
    {h4 : HasFourGroup G} (h : Nat.card ↥(invSubgroup hDT h4) = 8) :
    ∃ U : Subgroup G, U ≤ invSubgroup hDT h4 ∧ Nat.card U = 4 := by
  -- `↥V` is a `2`-group of cardinality `8 ≥ 2 ^ 2`, so it has a subgroup `H` of order `4`.
  obtain ⟨H, _hHle, hHcard⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card (p := 2) (n := 2)
    Nat.prime_two (isPGroup_invSubgroup hDT h4) (H := ⊤) (by rw [Subgroup.card_top, h]; norm_num)
  -- Push `H ≤ ↥V` forward along `V ↪ G`; the image is a subgroup of `G` of the same order.
  refine ⟨H.map (invSubgroup hDT h4).subtype, Subgroup.map_subtype_le H, ?_⟩
  rw [Subgroup.card_map_of_injective (invSubgroup hDT h4).subtype_injective, hHcard]
  norm_num

end Work.Hering.V
