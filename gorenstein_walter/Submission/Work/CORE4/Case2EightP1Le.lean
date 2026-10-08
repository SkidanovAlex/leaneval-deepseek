import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.NcardSubgroupsCardPrimeSq

namespace Work.CORE4

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- `⊢`-conjugation preserves the order of a subgroup: `|P ^ g| = |P|`. -/
theorem natCard_conjSub (G : Type) [Group G] (g : G) (P : Subgroup G) :
    Nat.card (Work.GW2.conjSub g P) = Nat.card P := by
  rw [Work.GW2.conjSub]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- Bender 1981, §4 (8), p. 225, "`p₁ ≤ p + 1`": in an abelian subgroup `A ≤ G` of order `p ^ 2`
and exponent `p`, the number of `G`-conjugates of `P ≤ A` (of order `p`) that lie in `A` is at
most `p + 1` (they are subgroups of `A` of order `p`, of which the elementary abelian group of
order `p ^ 2` has `p + 1`). -/
theorem Case2EightP1Le {G : Type} [Group G] [Finite G] (p : ℕ) (P A : Subgroup G)
    (hp : p.Prime) (hPA : P ≤ A) (hAcard : Nat.card A = p ^ 2)
    (hAexp : ∀ x ∈ A, x ^ p = 1) (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hPcard : Nat.card P = p) :
    Work.GW2.Case2EightP1 P A ≤ p + 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- `A` itself is an elementary abelian group of order `p ^ 2`.
  have hexpA : ∀ x : ↥A, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    simpa using hAexp (x : G) x.property
  have hcommA : ∀ a b : ↥A, a * b = b * a := by
    intro a b
    apply Subtype.ext
    simpa using hAcomm (a : G) a.property (b : G) b.property
  -- By `NcardSubgroupsCardPrimeSq`, `A` has exactly `p + 1` subgroups of order `p`.
  have hU : ({Y : Subgroup ↥A | Nat.card Y = p} : Set (Subgroup ↥A)).ncard = p + 1 := by
    have h := NcardSubgroupsCardPrimeSq p ↥A (by simpa using hAcard) hexpA hcommA
    simpa using h
  -- Each `G`-conjugate of `P` inside `A` is a subgroup of `A` of order `p`; the map
  -- `X ↦ X.subgroupOf A` is injective on them.
  rw [Work.GW2.Case2EightP1]
  refine le_trans ?_ (le_of_eq hU)
  refine Set.ncard_le_ncard_of_injOn (fun X : Subgroup G => X.subgroupOf A) ?_ ?_
  · intro X hX
    obtain ⟨hXA, g, rfl⟩ := hX
    change Nat.card ↥((Work.GW2.conjSub g P).subgroupOf A) = p
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXA).toEquiv]
    rw [natCard_conjSub, hPcard]
  · intro X hX Y hY hXY
    obtain ⟨hXA, -⟩ := hX
    obtain ⟨hYA, -⟩ := hY
    calc X = Subgroup.map A.subtype (X.subgroupOf A) :=
          (Subgroup.map_subgroupOf_eq_of_le hXA).symm
      _ = Subgroup.map A.subtype (Y.subgroupOf A) := congrArg _ hXY
      _ = Y := Subgroup.map_subgroupOf_eq_of_le hYA

end Work.CORE4
