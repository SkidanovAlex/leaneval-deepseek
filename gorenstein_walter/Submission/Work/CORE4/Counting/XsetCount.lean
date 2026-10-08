import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Counting.ElevenGW
import Submission.Work.CORE4.Counting.XConjCount
import Submission.Work.CORE4.Counting.XSdiffCount
import Submission.Work.CORE4.Counting.XArithNat

namespace Work.CORE4.Counting

/-- **The counting infrastructure of Bender 1981, §4 (11)–(12), p. 227.**

Let `P ≤ E` be a fixed order-`p` subgroup (`P ⊓ E = ⊥`, `P` commuting with `E`), `A ≤ P ⊔ E` a
subgroup containing `P`, `p₁ = #{X ≤ A : X ~ P}` the number of `G`-conjugates of `P` inside `A`,
and suppose `P ⊔ E` contains `(p₁ − 1) qk' + 1` conjugates of `P` of order `p` (Bender's (11),
proved as `Work.CORE4.Counting.ElevenGW` / `Count11`).  Then:

* the conjugates of `P` of order `p` inside `P ⊔ E` that are **not** inside `A` number
  `(p₁ − 1)(qk' − 1)` — this is Bender's set `𝒳` (his line "there are `(p₁−1)qk'` conjugates in
  `P×E`; those in `A` number `p₁`");
* for every `g : G`, the conjugate copy `conjSub g (P ⊔ E)` contains the same number
  `(p₁ − 1) qk' + 1` of conjugates of `P` of order `p` — this is Bender's "(11) applied to
  `X × E^g`".

Here `conjSub g K = K.map (MulAut.conj g).toMonoidHom` (`Work.GW2.conjSub`). -/
theorem XsetCount {G : Type} [Group G] [Finite G] (p qk' p1 : ℕ) (P E A : Subgroup G) :
    1 ≤ qk' → 1 ≤ p1 → A ≤ P ⊔ E →
      ({X : Subgroup G | Nat.card ↥X = p ∧ X ≤ P ⊔ E ∧ (∃ s : G, X = Work.GW2.conjSub s P)}.ncard
          = (p1 - 1) * qk' + 1) →
      ({X : Subgroup G | X ≤ A ∧ (∃ s : G, X = Work.GW2.conjSub s P)}.ncard = p1) →
      ({X : Subgroup G |
          Nat.card ↥X = p ∧ X ≤ P ⊔ E ∧ (∃ s : G, X = Work.GW2.conjSub s P) ∧ ¬ X ≤ A}.ncard
        = (p1 - 1) * (qk' - 1)) ∧
      (∀ g : G, {Y : Subgroup G |
          Nat.card ↥Y = p ∧ Y ≤ Work.GW2.conjSub g (P ⊔ E) ∧
            (∃ s : G, Y = Work.GW2.conjSub s P)}.ncard = (p1 - 1) * qk' + 1) := by
  intro hq hp1 hA hS hT
  -- The set `S` of order-`p` conjugates of `P` inside `P ⊔ E` has cardinality
  -- `(p1 - 1) * qk' + 1 ≠ 0`, hence is nonempty; an element of it is `conjSub s₀ P`, so the
  -- cardinality of `P` itself is `p`.
  have hSne : ({X : Subgroup G | Nat.card ↥X = p ∧ X ≤ P ⊔ E ∧
      (∃ s : G, X = Work.GW2.conjSub s P)} : Set (Subgroup G)) ≠ ∅ := by
    intro h0
    have hz : ({X : Subgroup G | Nat.card ↥X = p ∧ X ≤ P ⊔ E ∧
        (∃ s : G, X = Work.GW2.conjSub s P)} : Set (Subgroup G)).ncard = 0 := by
      rw [h0, Set.ncard_empty]
    rw [hS] at hz
    exact absurd hz (Nat.succ_ne_zero ((p1 - 1) * qk'))
  obtain ⟨X₀, hX₀card, -, s₀, hX₀eq⟩ := Set.nonempty_iff_ne_empty.mpr hSne
  have hPcard : Nat.card ↥P = p := by
    have h1 : Nat.card ↥(Work.GW2.conjSub s₀ P) = p := by rw [← hX₀eq]; exact hX₀card
    rwa [conjSub_card] at h1
  refine ⟨?_, ?_⟩
  · -- Bender's set `𝒳`: the difference of the two counted sets, using `T ⊆ S`.
    rw [XSdiffCount p P (P ⊔ E) A hPcard hA, hS, hT]
    exact XArithNat qk' p1 hq hp1
  · -- Conjugation by `g` is a bijection of the conjugates of `P` below `P ⊔ E` onto those
    -- below `conjSub g (P ⊔ E)`, so Bender's (11) transfers to every conjugate copy.
    intro g
    rw [XConjCount p P (P ⊔ E) g]
    exact hS

end Work.CORE4.Counting
