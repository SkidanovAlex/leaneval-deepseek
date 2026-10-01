import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_of_count
import Submission.Work.ZeroFreeTables.L52Hyp_six_level
import Submission.Work.ZeroFreeTables.L52Hyp_eighth_le4
import Submission.Work.LinnikAreas.DhCapped.L52Hyp_mono

/-!
# `L52Hyp` at levels `1/6` (all non-principal `χ`) and `1/8` (real `χ`), simultaneously

`L52Hyp_six_level` supplies, from Heath-Brown's Lemma 3.1 with `φ = 1/3`, a radius `δ₁` and a
threshold `q₁` such that `L52Hyp χ (1/6) ε δ₁` holds for every non-principal `χ` modulo `q ≥ q₁`.
`L52Hyp_eighth_le4` supplies, from Lemma 3.1 with `φ = 1/4`, a radius `δ₂` and threshold `q₂` such
that `L52Hyp χ (1/8) ε δ₂` holds for every non-principal `χ` modulo `q ≥ q₂` with `χ ^ 4 = 1`.

The hypothesis `L52Hyp χ c ε δ` is monotone *decreasing* in the radius `δ`
(`Work.LinnikAreas.DhCapped.L52Hyp_mono`): the window sum only grows with `δ`, so shrinking the
radius preserves the inequality.  Taking `δ = min δ₁ δ₂` and `q₀ = max q₁ q₂` therefore yields
both supplies with a single `δ`, and `χ ^ 2 = 1` implies `χ ^ 4 = 1`.
-/

namespace Work.ZeroFreeTables

theorem L52HypBoth (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → (Commons.NumberTheory.Linnik.L52Hyp χ (1 / 6) ε δ ∧
        (χ ^ 2 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1 / 8) ε δ)) := by
  obtain ⟨δ₁, hδ₁0, hδ₁1, q₁, hq₁⟩ := L52Hyp_six_level ε hε
  obtain ⟨δ₂, hδ₂0, hδ₂1, q₂, hq₂⟩ := L52Hyp_eighth_le4 ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁0 hδ₂0,
    lt_of_le_of_lt (min_le_left _ _) hδ₁1, max q₁ q₂, ?_⟩
  intro q hq _inst χ _instc hχ
  have hq₁' : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq₂' : q₂ ≤ q := le_trans (le_max_right _ _) hq
  refine ⟨?_, ?_⟩
  · exact Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ (min_le_left _ _)
      (hq₁ q hq₁' χ hχ)
  · intro hχ2
    have hχ4 : χ ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hχ2, one_pow]
    exact Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ (min_le_right _ _)
      (hq₂ q hq₂' χ hχ hχ4)

end Work.ZeroFreeTables
