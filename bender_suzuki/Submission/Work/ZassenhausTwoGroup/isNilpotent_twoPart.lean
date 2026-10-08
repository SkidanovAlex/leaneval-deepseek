import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

/-- `O_2(Q) = twoPart Q` is a `2`-group: it is (the image of) the `2`-core of `Q`, and the
`2`-core is a `π`-group for `π = (· = 2)` (`Work.Fitting.piCore_isPiNat`), i.e. its order is a
power of `2`; the image along the injective `Q.subtype` has the same order. -/
theorem isPGroup_twoPart {G : Type} [Group G] [Finite G] {Q : Subgroup G} :
    IsPGroup 2 ↥(Work.ZassenhausTwoGroup.twoPart Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  -- The order of `O_2(Q)` is a power of `2`.
  obtain ⟨k, hk⟩ := (Work.Fitting.isPiNat_prime_iff Nat.prime_two).mp
    (Work.Fitting.piCore_isPiNat ↥Q (fun q => q = 2))
  -- Passing to the image under the injective inclusion `Q.subtype` preserves the order.
  exact ⟨k, by
    rw [Work.ZassenhausTwoGroup.twoPart,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)]
    exact hk⟩

/-- `O_2(Q) = twoPart Q` is nilpotent: it is a finite `2`-group and every finite `p`-group is
nilpotent (`IsPGroup.isNilpotent`).

This is the "Sylow `2`-subgroup of `Q`" half of the decomposition `Q = O_2(Q) × O_{2'}(Q)`
used in Feit's theorem on Zassenhaus groups; it needs no hypothesis on `Q` itself, since the
`2`-core of an arbitrary finite group is always a `2`-group. -/
theorem isNilpotent_twoPart {G : Type} [Group G] [Finite G] {Q : Subgroup G} :
    Group.IsNilpotent (Work.ZassenhausTwoGroup.twoPart Q) :=
  IsPGroup.isNilpotent (p := 2) (isPGroup_twoPart)

end Work.ZassenhausTwoGroup
