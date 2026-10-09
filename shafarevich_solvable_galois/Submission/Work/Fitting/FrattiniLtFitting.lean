/-
Copyright (c) 2025. All rights reserved.

# The Frattini subgroup is properly contained in the Fitting subgroup

For a nontrivial finite solvable group `G` we prove `Φ(G) < F(G)` (Huppert, *Endliche Gruppen
I*, III.4.2(c); Schmidt–Wingberg, Proposition 17).

Together with the supplement lemma (`exists_supplement_of_not_le_frattini`, Huppert III.3.2(b),
Schmidt–Wingberg Proposition 16) this gives the group-theoretic input of Ore's proof of
Shafarevich's theorem: `F(G)` has a proper supplement `U < G` with `F(G)·U = G`.

## Main results

* `card_quotient_lt` : `|G ⧸ A| < |G|` for `A ≠ ⊥`;
* `frattini_lt_fitting` : `Φ(G) < F(G)` for finite solvable nontrivial `G`.
-/
import Mathlib
import Submission.Work.Fitting.Basic
import Submission.Work.Fitting.PCore
import Submission.Work.Fitting.FittingEqPCore
import Submission.Work.Fitting.FittingQuotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Fitting

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
open scoped Classical
open Subgroup

universe u

variable {G : Type*} [Group G]

/-- A nontrivial normal subgroup has a strictly smaller quotient. -/
theorem card_quotient_lt [Finite G] {A : Subgroup G} [A.Normal] (hA : A ≠ ⊥) :
    Nat.card (G ⧸ A) < Nat.card G := by
  have h1 : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).mpr hA
  have h2 : 0 < A.index := Nat.pos_of_ne_zero A.index_ne_zero_of_finite
  rw [← Subgroup.index_eq_card, ← Subgroup.index_mul_card]
  exact lt_mul_of_one_lt_right h2 h1

/-- `⊤ ≠ ⊥` as subgroups of a nontrivial group. -/
theorem top_ne_bot_of_not_subsingleton (h : ¬ Subsingleton G) : (⊤ : Subgroup G) ≠ ⊥ := by
  intro hbot
  refine h ⟨fun x y => ?_⟩
  have hx : x = 1 := Subgroup.mem_bot.mp (hbot ▸ (Subgroup.mem_top x : x ∈ (⊤ : Subgroup G)))
  have hy : y = 1 := Subgroup.mem_bot.mp (hbot ▸ (Subgroup.mem_top y : y ∈ (⊤ : Subgroup G)))
  rw [hx, hy]

/-- **Huppert III.4.2(c)**: the Frattini subgroup of a nontrivial finite solvable group is a
proper subgroup of the Fitting subgroup. -/
theorem frattini_lt_fitting (G : Type u) [Group G] [Finite G] [Group.IsSolvable G]
    (h : ¬ Subsingleton G) : frattini G < fitting G := by
  classical
  have main : ∀ n : ℕ, ∀ (H : Type u) [Group H] [Finite H] [Group.IsSolvable H],
      Nat.card H = n → ¬ Subsingleton H → frattini H < fitting H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H _ _ _ hcard hntriv
      refine lt_of_le_of_ne frattini_le_fitting ?_
      intro heq
      obtain ⟨A, hAn, hAne, hAmin⟩ := exists_minimal_normal H hntriv
      haveI := hAn
      obtain ⟨p, hp, hcomm, -⟩ :=
        Work.GroupTheory.isElementaryAbelian_of_minimal_normal H A hAne hAmin
      have hAle : A ≤ frattini H := by
        rw [heq]
        exact le_fitting hAn (isNilpotent_of_isMulCommutative hcomm)
      by_cases hAtop : A = ⊤
      · -- `A = ⊤` would force `Φ(H) = ⊤`
        exact frattini_ne_top (G := H) hntriv (top_le_iff.mp (hAtop ▸ hAle))
      · -- descend to `H ⧸ A`, which is a strictly smaller solvable group
        have hquot : ¬ Subsingleton (H ⧸ A) := by
          intro hs
          refine hAtop (eq_top_iff.mpr fun x _ => ?_)
          have hx : (QuotientGroup.mk' A) x = 1 := Subsingleton.elim _ _
          simpa [QuotientGroup.mk'_apply] using hx
        have hcardA : Nat.card (H ⧸ A) < n := by
          rw [← hcard]
          exact card_quotient_lt hAne
        have hid := ih (Nat.card (H ⧸ A)) hcardA (H ⧸ A) rfl hquot
        have h1 : (fitting H).map (QuotientGroup.mk' A) ≤ frattini (H ⧸ A) := by
          rw [← heq]
          exact frattini_map_le A
        have h2 : (fitting H).map (QuotientGroup.mk' A) = fitting (H ⧸ A) :=
          fitting_map_quotient A hAle
        exact hid.2 (h2 ▸ h1)
  exact main (Nat.card G) G rfl h

end Work.Fitting
