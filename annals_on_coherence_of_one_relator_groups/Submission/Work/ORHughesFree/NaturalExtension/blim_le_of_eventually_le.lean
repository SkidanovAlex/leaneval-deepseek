import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs

namespace Work.ORHughesFree.NaturalExtension

/-- If a bounded real-valued sequence is eventually at most `y` along `atTop`, then its
ultralimit along any ultrafilter containing the cofinite filter is at most `y`.

The ultralimit is `sSup {r | {i | r ≤ f i} ∈ ω}`; every `r` in that set satisfies `r ≤ y`,
because otherwise `{i | r ≤ f i}` would be `ω`-large but disjoint from the `ω`-large set
`{i | f i ≤ y}` given by the eventual bound. -/
theorem blim_le_of_eventually_le (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop)
    {f : ℕ → ℝ} {M y : ℝ} (hf : ∀ i, |f i| ≤ M)
    (hy : ∀ᶠ i in Filter.atTop, f i ≤ y) : blim ω f ≤ y := by
  set S : Set ℝ := {r : ℝ | {i | r ≤ f i} ∈ ω} with hS
  have hblim : blim ω f = sSup S := rfl
  rw [hblim]
  -- `y` is an upper bound of `S`.
  have hub : ∀ r ∈ S, r ≤ y := by
    intro r hr
    by_contra hlt
    rw [not_le] at hlt
    -- The eventual bound gives an `ω`-large set on which `f ≤ y`.
    have hyω : {i : ℕ | f i ≤ y} ∈ (ω : Filter ℕ) := hω hy
    -- Membership of `r` in `S` says `{i | r ≤ f i}` is `ω`-large.
    have hrω : {i : ℕ | r ≤ f i} ∈ (ω : Filter ℕ) := hr
    -- These two sets are disjoint when `y < r`.
    have hdisj : {i : ℕ | r ≤ f i} ∩ {i : ℕ | f i ≤ y} = ∅ := by
      ext i
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro hri hiy
      linarith
    have hemp : (∅ : Set ℕ) ∈ (ω : Filter ℕ) := by
      rw [← hdisj]
      exact Filter.inter_mem hrω hyω
    exact Ultrafilter.empty_notMem hemp
  -- `S` is nonempty: `-M` works since `|f i| ≤ M` makes `{-M ≤ f i}` all of `ℕ`.
  have hne : S.Nonempty := by
    refine ⟨-M, ?_⟩
    rw [hS]
    simp only [Set.mem_ofPred_eq]
    have h0 : {i : ℕ | -M ≤ f i} = Set.univ := by
      ext i; exact iff_true_intro (neg_le_of_abs_le (hf i))
    rw [h0]; exact Filter.univ_mem
  exact csSup_le hne hub

end Work.ORHughesFree.NaturalExtension
