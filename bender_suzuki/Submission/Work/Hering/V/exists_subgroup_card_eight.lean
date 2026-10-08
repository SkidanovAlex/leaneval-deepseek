import Mathlib
import Submission.Work.Hering.V.card_eq_two_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `V = Inv(G) ∪ {1}` contains a subgroup of order `8`

`V = invSubgroup hDT h4` is a finite `2`-group (`Work.Hering.isPGroup_invSubgroup`), so Sylow's
first theorem in the form `Sylow.exists_subgroup_le_card_pow_prime_of_le_card` produces, inside
`V` and for every `n` with `2 ^ n ≤ |V|`, a subgroup of cardinality `2 ^ n`. Taking `n = 3` and
transporting the resulting subgroup of `↥V` back to `G` along the injection `V ↪ G` gives a true
subgroup of `G` of order `8`, contained in `V`.
-/

set_option autoImplicit false

namespace Work.Hering.V

/-- If `V = Inv(G) ∪ {1}` has at least `8` elements, then it contains a subgroup of `G` of order
`8`. -/
theorem exists_subgroup_card_eight {G : Type*} [Group G] (hDT : DTInv G) (h4 : HasFourGroup G)
    [Finite G] (h : 8 ≤ Nat.card ↥(invSubgroup hDT h4)) :
    ∃ U : Subgroup G, U ≤ invSubgroup hDT h4 ∧ Nat.card U = 8 := by
  -- `↥V` is a `2`-group of cardinality `≥ 2 ^ 3 = 8`, so it has a subgroup `H` of order `8`.
  obtain ⟨H, _hHle, hHcard⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card (p := 2) (n := 3)
    Nat.prime_two (isPGroup_invSubgroup hDT h4) (H := ⊤) (by simpa using h)
  -- Push `H ≤ ↥V` forward along `V ↪ G`; the image is a subgroup of `G` of the same order.
  refine ⟨H.map (invSubgroup hDT h4).subtype, ?_, ?_⟩
  · exact Subgroup.map_subtype_le H
  · rw [Subgroup.card_map_of_injective (invSubgroup hDT h4).subtype_injective, hHcard]
    norm_num

end Work.Hering.V
