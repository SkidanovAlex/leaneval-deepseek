import Mathlib
import Submission.Work.CORE4.Counting.Count11

namespace Work.CORE4.Counting

theorem XSdiffCount {G : Type} [Group G] [Finite G] (p : ℕ) (Q D A : Subgroup G)
    (hQD : Nat.card ↥Q = p) (hA : A ≤ D) :
    ({X : Subgroup G | Nat.card ↥X = p ∧ X ≤ D ∧ (∃ s : G, X = Work.GW2.conjSub s Q) ∧
        (¬ X ≤ A)}.ncard)
      = ({X : Subgroup G | Nat.card ↥X = p ∧ X ≤ D ∧ (∃ s : G, X = Work.GW2.conjSub s Q)}.ncard
        - ({X : Subgroup G | X ≤ A ∧ (∃ s : G, X = Work.GW2.conjSub s Q)}.ncard)) := by
  -- Every conjugate of `Q` has order `p`, by transport of the order along conjugation.
  have hcard : ∀ s : G, Nat.card ↥(Work.GW2.conjSub s Q) = p := by
    intro s; rw [conjSub_card]; exact hQD
  -- The set `T = {X ≤ A : X ~ Q}` of conjugates lying inside `A` is contained in the ambient
  -- set `S = {X ≤ D : |X| = p, X ~ Q}` of conjugates: `A ≤ D` and `|X^s| = |Q| = p`.
  have hTsub : {X : Subgroup G | X ≤ A ∧ (∃ s : G, X = Work.GW2.conjSub s Q)}
      ⊆ {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ D ∧ (∃ s : G, X = Work.GW2.conjSub s Q)} := by
    rintro X ⟨hXA, s, rfl⟩
    exact ⟨hcard s, le_trans hXA hA, s, rfl⟩
  -- The required set is exactly `S \ T`: since membership in `T` demands `X ~ Q` and membership
  -- in `S` already supplies that, `¬ (X ≤ A ∧ X ~ Q)` reduces to `¬ X ≤ A` on `S`.
  have hTeq : {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ D ∧ (∃ s : G, X = Work.GW2.conjSub s Q) ∧ ¬ X ≤ A}
      = {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ D ∧ (∃ s : G, X = Work.GW2.conjSub s Q)}
        \ {X : Subgroup G | X ≤ A ∧ (∃ s : G, X = Work.GW2.conjSub s Q)} := by
    ext X
    constructor
    · rintro ⟨hc, hD, hconj, hnA⟩
      exact ⟨⟨hc, hD, hconj⟩, fun h => hnA h.1⟩
    · rintro ⟨⟨hc, hD, hconj⟩, hnotT⟩
      exact ⟨hc, hD, hconj, fun hXA => hnotT ⟨hXA, hconj⟩⟩
  -- `Subgroup G` is finite, so `|S \ T| = |S| - |T|`.
  rw [hTeq, Set.ncard_sdiff hTsub]

end Work.CORE4.Counting
