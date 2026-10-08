import Mathlib
import Submission.Work.ThompsonFrobenius.BlueprintZJ
import Submission.Work.NPC.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThompsonFrobenius`: Glauberman–Thompson Theorem D, definitions

Route of the area (`NOTES_LEAD_bs_thompson.md`): Thompson's theorem is deduced from the
Glauberman–Thompson normal `p`-complement theorem (Glauberman 1968, Theorem D) with the `ZJ` step
supplied by `GlaubermanZJProp`.  This module fixes the vocabulary of that theorem; the steps of the
minimal-counterexample proof live in one file per step (`GTMinimal.*`).

* `GTStatement p G`: for every Sylow `p`-subgroup `P` of `G`, `p`-nilpotency of
  `N_G(Z(J(P)))` forces `p`-nilpotency of `G`.
* `GTMinimal p G P`: `G` is a counterexample of least order with that property, with the induction
  hypothesis `ih` for all finite groups of smaller cardinal.
-/

set_option autoImplicit false

open Submission.Blueprint

namespace Work.ThompsonFrobenius

/-- The Glauberman–Thompson theorem (Theorem D) for a single group. -/
def GTStatement (p : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ P : Sylow p G,
    Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (ZJ (P : Subgroup G) : Set G)) →
    Work.NPC.HasNormalPComplement p G

/-- A minimal counterexample to the Glauberman–Thompson theorem. -/
structure GTMinimal (p : ℕ) (G : Type) [Group G] [Finite G] (P : Sylow p G) : Prop where
  /-- `p` is prime -/
  prime : p.Prime
  /-- `p` is odd -/
  ne_two : p ≠ 2
  /-- the `ZJ`-normalizer hypothesis holds -/
  hyp : Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (ZJ (P : Subgroup G) : Set G))
  /-- `G` is not `p`-nilpotent -/
  not_npc : ¬ Work.NPC.HasNormalPComplement p G
  /-- the induction hypothesis for smaller groups -/
  ih : ∀ (X : Type) [Group X] [Finite X], Nat.card X < Nat.card G → GTStatement p X

end Work.ThompsonFrobenius
