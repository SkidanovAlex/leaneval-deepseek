import Mathlib
import Submission.Work.CORE4.Counting.Count11

namespace Work.CORE4.Counting

/-- **Counting conjugates below a conjugate subgroup.**

Conjugation by `g` is a bijection of the set of `G`-conjugates of `Q` of order `p` that lie
below `W` onto the set of those that lie below `conjSub g W`; hence the two sets have the same
cardinality.  (Helper lemmas `conjSub_card`, `conjSub_mul`, `conjSub_inv_conjSub` and
`ncard_conjSub_image` come from `Work.CORE4.Counting.Count11`.) -/
theorem XConjCount {G : Type} [Group G] [Finite G] (p : ℕ) (Q W : Subgroup G) (g : G) :
    ({Y : Subgroup G | Nat.card ↥Y = p ∧ Y ≤ Work.GW2.conjSub g W ∧
        (∃ s : G, Y = Work.GW2.conjSub s Q)}.ncard
      = {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ W ∧
        (∃ s : G, X = Work.GW2.conjSub s Q)}.ncard) := by
  have hset : {Y : Subgroup G | Nat.card ↥Y = p ∧ Y ≤ Work.GW2.conjSub g W ∧
        (∃ s : G, Y = Work.GW2.conjSub s Q)}
      = Work.GW2.conjSub g '' {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ W ∧
        (∃ s : G, X = Work.GW2.conjSub s Q)} := by
    ext Y
    constructor
    · rintro ⟨hYcard, hYle, s, hYs⟩
      refine ⟨Work.GW2.conjSub g⁻¹ Y, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [conjSub_card]; exact hYcard
      · have h1 : Work.GW2.conjSub g⁻¹ Y ≤ Work.GW2.conjSub g⁻¹ (Work.GW2.conjSub g W) :=
          Subgroup.map_mono hYle
        rwa [conjSub_inv_conjSub] at h1
      · refine ⟨g⁻¹ * s, ?_⟩
        rw [hYs, ← conjSub_mul]
      · simpa using conjSub_inv_conjSub g⁻¹ Y
    · rintro ⟨X, ⟨hXcard, hXle, s, hXs⟩, rfl⟩
      exact ⟨by rw [conjSub_card]; exact hXcard,
        Subgroup.map_mono hXle,
        ⟨g * s, by rw [hXs, conjSub_mul]⟩⟩
  rw [hset, ncard_conjSub_image]

end Work.CORE4.Counting
