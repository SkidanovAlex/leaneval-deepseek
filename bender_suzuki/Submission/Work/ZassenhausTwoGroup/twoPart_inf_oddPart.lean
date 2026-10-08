import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.Fitting.piCore_inf_eq_bot_of_coprime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `twoPart Q ⊓ oddPart Q = ⊥`

For any subgroup `Q` of a finite group `G` the `2`-core `O_2(Q)` and the `2'`-core `O_{2'}(Q)`
intersect trivially.  Concretely, `K = O_2(Q) ⊓ O_{2'}(Q)` is contained in each core, so `|K|`
divides both `|O_2(Q)|` (a power of `2`) and `|O_{2'}(Q)|` (odd); a prime divisor of `|K|` would
have to be both `2` and not `2`, so `|K| = 1` and `K = ⊥`.

This is `Work.Fitting.piCore_inf_eq_bot_of_coprime` for the disjoint predicates
`π = (· = 2)` and `σ = (· ≠ 2)`, pushed forward from `Q` to `G` along the (injective) inclusion
`Q.subtype`: `Subgroup.map_inf` turns the image of the intersection into the intersection of the
images, and images of `⊥` are `⊥`.  Note that no nilpotency of `Q` is used.
-/

namespace Work.ZassenhausTwoGroup

/-- `O_2(Q) ⊓ O_{2'}(Q) = ⊥`: the `2`-part and the odd part of `Q` are disjoint, because their
orders are `2`- and `2'`-numbers respectively. -/
theorem twoPart_inf_oddPart {G : Type} [Group G] [Finite G] {Q : Subgroup G} :
    Work.ZassenhausTwoGroup.twoPart Q ⊓ Work.ZassenhausTwoGroup.oddPart Q = ⊥ := by
  -- Inside `Q`, the `2`-core and the `2'`-core are disjoint (`π = (· = 2)`, `σ = (· ≠ 2)`).
  have hbot : Work.Fitting.pCore 2 ↥Q ⊓ Work.Fitting.pPrimeCore 2 ↥Q = ⊥ :=
    Work.Fitting.piCore_inf_eq_bot_of_coprime (fun q => q = 2) (fun q => q ≠ 2) ↥Q
      (fun _ hp hp' => hp' hp)
  -- `twoPart`/`oddPart` are the images of these two cores along the injective map `Q.subtype`.
  unfold Work.ZassenhausTwoGroup.twoPart Work.ZassenhausTwoGroup.oddPart
  rw [← Subgroup.map_inf _ _ Q.subtype (Subgroup.subtype_injective Q), hbot, Subgroup.map_bot]

end Work.ZassenhausTwoGroup
