import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausTwoGroup.twoPoint_ne_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.ZData.three_le_card_twoPoint`

**Z0** of the lead's design (`_design/PSL2Core.lean`): in a finite simple group with split
rank-one Zassenhaus data, the two-point stabiliser `D = twoPoint H t` has order at least `3`.

Indeed `D ≠ ⊥` (`Work.ZassenhausTwoGroup.twoPoint_ne_bot`, from Frobenius' theorem and
simplicity) and `|D|` is odd (strong embedding with `t ∉ H`), so `|D| ≥ 2` is odd, hence
`|D| ≥ 3`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2.ZData

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **Z0.** `3 ≤ |D|`. -/
theorem three_le_card_twoPoint [IsSimpleGroup G] (h : IsSplitRankOne H Q t)
    (hz : IsZassenhaus H) : 3 ≤ Nat.card (twoPoint H t) := by
  have hne : twoPoint H t ≠ ⊥ := Work.ZassenhausTwoGroup.twoPoint_ne_bot h hz
  -- an element of `D` different from `1`
  have hex : ∃ x : G, x ∈ (twoPoint H t : Set G) ∧ x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hne (Subgroup.ext (fun x => ⟨fun hx => Subgroup.mem_bot.mpr (hcon x hx),
      fun hx => by rw [Subgroup.mem_bot] at hx; rw [hx]; exact (twoPoint H t).one_mem⟩))
  obtain ⟨x, hx, hx1⟩ := hex
  have h2 : 2 ≤ Nat.card (twoPoint H t) := by
    have hnat : Nat.card (twoPoint H t) = (twoPoint H t : Set G).ncard :=
      Nat.card_coe_set_eq _
    rw [hnat]
    have hsub : ({(1 : G), x} : Set G) ⊆ (twoPoint H t : Set G) := by
      intro y hy
      rcases hy with rfl | rfl
      · exact (twoPoint H t).one_mem
      · exact hx
    have hc : ({(1 : G), x} : Set G).ncard = 2 := Set.ncard_pair hx1.symm
    calc 2 = ({(1 : G), x} : Set G).ncard := hc.symm
      _ ≤ (twoPoint H t : Set G).ncard := Set.ncard_le_ncard hsub
  have hodd : Odd (Nat.card (twoPoint H t)) := h.stronglyEmbedded.2.2 t h.not_mem
  obtain ⟨k, hk⟩ := hodd
  omega

end Work.ZassenhausPSL2.ZData
