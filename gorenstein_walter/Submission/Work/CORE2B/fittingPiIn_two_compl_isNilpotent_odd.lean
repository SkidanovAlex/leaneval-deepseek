import Mathlib
import Submission.Work.CORE2B.L27_solvable_base
import Submission.Work.CORE2B.L27cf_centralizes_odd_pi_part

/-!
# `F_{2'}(N)` is nilpotent of odd order

For any subgroup `N` of a finite group `G`, the `2'`-part of the Fitting subgroup,
`F_{2'}(N) = O_{2'}(F(N))`, is nilpotent and of odd order.

* Nilpotency: `F_{2'}(N) ≤ F(N)`, and a subgroup of the nilpotent group `F(N)` is nilpotent.
* Odd order: `F_{2'}(N)` is the image of the characteristic subgroup `O_{2'}(F(N))` of
  `↥N`, which is a `{2}ᶜ`-group, hence of odd order.

The two ingredients are the area's `L27cf_isNilpotent_fitting` (nilpotency of `F(N)`) and
`L27cf_odd_card_fittingPiIn` (oddness), assembled here as the general statement used by
`L29FaithfulProp_proved`.
-/

namespace Work.CORE2B

open Subgroup

set_option linter.style.haveILetI false

/-- `F_{2'}(N) ≤ F(N)` inside `G`. -/
theorem fittingPiIn_two_compl_le_fittingIn {G : Type} [Group G]
    (N : Subgroup G) :
    Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) N ≤ Work.GW2.fittingIn N := by
  rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi]
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

theorem fittingPiIn_two_compl_isNilpotent_odd {G : Type} [Group G] [Finite G]
    (N : Subgroup G) :
    Group.IsNilpotent ↥(Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) N) ∧
      Odd (Nat.card (Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) N)) := by
  -- `F(N)` is nilpotent, hence so is its image `F(N) ↪ G`
  have hFnil : Group.IsNilpotent ↥(Work.GW2.fittingIn N) := by
    rw [Work.GW2.fittingIn]
    exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective (Work.GW2.fitting ↥N)
      N.subtype N.subtype_injective)).mp (L27cf_isNilpotent_fitting (G := ↥N))
  refine ⟨?_, ?_⟩
  · -- a subgroup of the nilpotent group `F(N)` is nilpotent
    haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn N) := hFnil
    exact (Group.isNilpotent_congr
      (Subgroup.subgroupOfEquivOfLe (fittingPiIn_two_compl_le_fittingIn N))).mp inferInstance
  · -- `F_{2'}(N)` is a `{2}ᶜ`-group, hence has odd order
    exact L27cf_odd_card_fittingPiIn (σ := ({2}ᶜ : Set ℕ)) (fun _ hp => hp) N

end Work.CORE2B
