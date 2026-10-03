import Mathlib
import Submission.Work.KMTPlan.A6.lacWindow_card

namespace Work.KMTPlan.A6

open Finset

/-- **Counting a multiplicative window `(A, 16A)` of a lacunary sequence.**

This is the `16`-window companion of `Work.KMTPlan.A6.lacWindow_card` (which counts the
half-open window `[A, 8A)`).  It is deduced from it by splitting the interval:
`(A, 16A) = (A, 8A) ∪ [2A, 16A)`, both pieces being of the form counted by `lacWindow_card`
(the second one at the parameter `2A`), so that the same constant works twice and the answer is
`2 * (log 9 / log Λ + 1)`.

For `Λ > 1` and a `Λ`-lacunary sequence `a` with `a n ≥ 1`, the number of indices `n < K` with
`A < ⌊a n⌋ < 16 A` is bounded by a constant depending on `Λ` only, uniformly in `K` and `A > 0`. -/
theorem lacWindowCard16 (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → NNReal), PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∀ (K : ℕ) (A : ℝ), 0 < A →
      (((Finset.range K).filter (fun n => A < (Nat.floor (a n) : ℝ) ∧
          (Nat.floor (a n) : ℝ) < 16 * A)).card : ℝ) ≤ C := by
  obtain ⟨C₈, hC₈pos, hC₈⟩ := lacWindow_card Λ hΛ
  refine ⟨2 * C₈, by linarith, ?_⟩
  intro a ha ha1 K A hA
  set S := (Finset.range K).filter (fun n => A < (Nat.floor (a n) : ℝ) ∧
        (Nat.floor (a n) : ℝ) < 16 * A) with hS
  set S₁ := (Finset.range K).filter (fun n => A ≤ (Nat.floor (a n) : ℝ) ∧
        (Nat.floor (a n) : ℝ) < 8 * A) with hS1
  set S₂ := (Finset.range K).filter (fun n => 2 * A ≤ (Nat.floor (a n) : ℝ) ∧
        (Nat.floor (a n) : ℝ) < 16 * A) with hS2
  -- the window `(A, 16A)` is covered by the two windows counted by `lacWindow_card`
  have hsub : S ⊆ S₁ ∪ S₂ := by
    intro m hm
    have hm' := Finset.mem_filter.mp hm
    have hrange : m ∈ Finset.range K := hm'.1
    have hlo : A < (Nat.floor (a m) : ℝ) := hm'.2.1
    have hhi : (Nat.floor (a m) : ℝ) < 16 * A := hm'.2.2
    rcases lt_or_ge ((Nat.floor (a m) : ℝ)) (8 * A) with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hrange, le_of_lt hlo, h⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hrange, by linarith, hhi⟩)
  have hcard : (S.card : ℝ) ≤ (S₁.card : ℝ) + (S₂.card : ℝ) := by
    have h1 : S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsub
    have h2 : (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
    have h3 : (S.card : ℝ) ≤ ((S₁ ∪ S₂).card : ℝ) := by exact_mod_cast h1
    have h4 : (((S₁ ∪ S₂).card : ℕ) : ℝ) ≤ (S₁.card : ℝ) + (S₂.card : ℝ) := by
      exact_mod_cast h2
    linarith
  have hb1 : (S₁.card : ℝ) ≤ C₈ := by
    simpa only [hS1] using hC₈ a ha ha1 K A hA
  have hb2 : (S₂.card : ℝ) ≤ C₈ := by
    have h := hC₈ a ha ha1 K (2 * A) (by linarith)
    rw [show (8 : ℝ) * (2 * A) = 16 * A by ring] at h
    simpa only [hS2] using h
  linarith

end Work.KMTPlan.A6
