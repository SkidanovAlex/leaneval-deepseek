import Mathlib

namespace Work.EQ

open Set

/-- The `M`-window restriction of a word `ℤ → Bool` to the `2*M` positions `-M, …, M-1`,
encoded as `Fin (2*M)`. -/
private def window (M : ℕ) (σ : ℤ → Bool) : Fin (2*M) → Bool := fun i => σ ((i : ℤ) - (M : ℤ))

/-- Words that are `true` on both tails `[M, ∞)` and `(-∞, -M]`. -/
private def good (M : ℕ) : Set (ℤ → Bool) :=
  {σ | (∀ n : ℤ, (M : ℤ) ≤ n → σ n = true) ∧ (∀ n : ℤ, n ≤ -((M : ℤ)) → σ n = true)}

/-- For a fixed `M`, the words that are `true` on both tails are determined by their values on
the window `{-M, …, M-1}`, so there are only countably many of them. -/
private lemma good_countable (M : ℕ) : (good M).Countable := by
  have hg : Function.Injective (fun σ : ↑(good M) => window M σ.1) := by
    intro σ τ h
    apply Subtype.ext
    funext n
    rcases σ.2 with ⟨hσp, hσn⟩
    rcases τ.2 with ⟨hτp, hτn⟩
    by_cases hn : -((M : ℤ)) ≤ n ∧ n < (M : ℤ)
    · obtain ⟨hn1, hn2⟩ := hn
      have hge : 0 ≤ n + (M : ℤ) := by linarith
      have hlt : (n + (M : ℤ)).toNat < 2*M := by
        rw [Int.toNat_lt hge]; push_cast; linarith
      have key := congrFun h ⟨(n + (M : ℤ)).toNat, hlt⟩
      simp only [window] at key
      have hcast : (((n + (M : ℤ)).toNat : ℕ) : ℤ) = n + (M : ℤ) := Int.toNat_of_nonneg hge
      rw [hcast] at key
      have : n + (M : ℤ) - (M : ℤ) = n := by ring
      rw [this] at key
      exact key
    · rw [not_and_or] at hn
      rcases hn with hn | hn
      · have hle : n ≤ -((M : ℤ)) := le_of_lt (not_le.mp hn)
        rw [hσn n hle, hτn n hle]
      · have hle : (M : ℤ) ≤ n := not_lt.mp hn
        rw [hσp n hle, hτp n hle]
  exact hg.countable

/-- **The set of words that are eventually `true` in both directions is countable.**

A word `σ : ℤ → Bool` for which there is `M : ℕ` with `σ n = true` for all `n ≥ M` and for all
`n ≤ -M` is determined by its restriction to the finite interval `{-M, …, M-1}` (the two tails
being constant `true`), so the set of such words is the union over `M ∈ ℕ` of the images of the
finite types `Fin (2*M) → Bool`, hence countable.

Example of a Mathlib route: rewrite the set as `⋃ M, {σ | (∀ n ≥ M, σ n = true) ∧
(∀ n ≤ -M, σ n = true)}` (`Set.countable_iUnion`), and for each `M` either use
`Set.Countable.mono` with `Set.countable_range` of the map
`w : Fin (2*M) → Bool ↦ fun n => if -M ≤ n ∧ n < M then w ⟨(n+M).toNat, _⟩ else true`, or build
an injection into `Σ M : ℕ, (Fin (2*M) → Bool)` and use `Function.Injective.countable`. -/
theorem countable_eventually_true_words :
    ({σ : ℤ → Bool | ∃ M : ℕ, (∀ n : ℤ, (M : ℤ) ≤ n → σ n = true) ∧
      (∀ n : ℤ, n ≤ -((M : ℤ)) → σ n = true)} : Set (ℤ → Bool)).Countable := by
  have hS : ({σ : ℤ → Bool | ∃ M : ℕ, (∀ n : ℤ, (M : ℤ) ≤ n → σ n = true) ∧
      (∀ n : ℤ, n ≤ -((M : ℤ)) → σ n = true)} : Set (ℤ → Bool)) = ⋃ M : ℕ, good M := by
    ext σ; simp [good, Set.mem_iUnion]
  rw [hS]
  exact Set.countable_iUnion (fun M => good_countable M)

end Work.EQ
