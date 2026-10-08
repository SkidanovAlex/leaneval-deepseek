import Mathlib
import Submission.Work.CORE3.Defs

/-!
# CORE3: every 2-subgroup of `Ĥ` has order at most 8

In the subcase `V = O₂(Ĥ)` of Bender 1981 §3, the Sylow 2-subgroup `S` of the ambient group
satisfies `|S| = 8` (`Work.GW2.Case1bData.S8`).  Since `S` is a Sylow 2-subgroup of `G`, every
2-subgroup of `G` --- in particular every 2-subgroup of `Ĥ` --- has order at most `|S| = 8`.

The argument only uses Sylow's theorem (`IsPGroup.exists_le_sylow` and the cardinality formula
`Sylow.card_eq_multiplicity`); note that the hypothesis `P ≤ Ĥ` is not needed for the bound,
which in fact holds for every 2-subgroup of `G`.
-/

namespace Work.CORE3

open Subgroup

/-- Every `2`-subgroup of `G` has cardinality at most that of any Sylow `2`-subgroup of `G`:
it lies in a Sylow `2`-subgroup, and any two Sylow subgroups have the same cardinality. -/
theorem card_le_card_of_isPGroup_two_le_sylow {G : Type} [Group G] [Finite G]
    (S : Sylow 2 G) {P : Subgroup G} (hP2 : IsPGroup 2 P) :
    Nat.card P ≤ Nat.card (S : Subgroup G) := by
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  have hQS : Nat.card (Q : Subgroup G) = Nat.card (S : Subgroup G) := by
    rw [Q.card_eq_multiplicity, S.card_eq_multiplicity]
  calc Nat.card P ≤ Nat.card (Q : Subgroup G) := Subgroup.card_le_of_le hPQ
    _ = Nat.card (S : Subgroup G) := hQS

theorem card_le_eight_of_isPGroup_two_le_Hhat {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case1bData B) {P : Subgroup G}
    (hP : P ≤ B.Hhat) (hP2 : IsPGroup 2 P) : Nat.card P ≤ 8 := by
  have h := card_le_card_of_isPGroup_two_le_sylow B.S hP2
  rw [D.S8] at h
  exact h

end Work.CORE3
