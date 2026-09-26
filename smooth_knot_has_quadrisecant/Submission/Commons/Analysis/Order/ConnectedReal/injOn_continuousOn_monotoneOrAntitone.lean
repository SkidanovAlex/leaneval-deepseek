import Mathlib.Analysis.Normed.Order.Lattice

set_option linter.unusedVariables false

namespace Commons.Analysis.Order.ConnectedReal

/-- A continuous injective real function on a preconnected (hence interval-like) subset of `ℝ`
is strictly monotone either increasing or decreasing. -/
theorem injOn_continuousOn_monotoneOrAntitone {s : Set ℝ} (hsopen : IsOpen s)
    (hsconn : IsPreconnected s) {f : ℝ → ℝ}
    (hcont : ContinuousOn f s) (hinj : Set.InjOn f s) :
    (∀ ⦃a b : ℝ⦄, a ∈ s → b ∈ s → a < b → f a < f b) ∨
    (∀ ⦃a b : ℝ⦄, a ∈ s → b ∈ s → a < b → f b < f a) := by
  classical
  by_cases hinc : ∀ ⦃a b : ℝ⦄, a ∈ s → b ∈ s → a < b → f a < f b
  · exact Or.inl hinc
  · push Not at hinc
    rcases hinc with ⟨a₀, b₀, ha₀s, hb₀s, hab₀, hlt⟩
    have hle : f b₀ ≤ f a₀ := hlt
    refine Or.inr ?_
    intro a b ha hb hab
    let m : ℝ := min a a₀
    let M : ℝ := max b b₀
    have hmM : m ≤ M := by
      dsimp [m, M]
      exact le_trans (min_le_left a a₀) (le_trans hab.le (le_max_left b b₀))
    have hm₀s : m ∈ s := by
      rcases le_total a a₀ with h | h
      · simpa [m, min_eq_left h] using ha
      · simpa [m, min_eq_right h] using ha₀s
    have hMs : M ∈ s := by
      rcases le_total b b₀ with h | h
      · simpa [M, max_eq_right h] using hb₀s
      · simpa [M, max_eq_left h] using hb
    have hord : s.OrdConnected := hsconn.ordConnected
    have hullsub : Set.Icc m M ⊆ s := hord.out' hm₀s hMs
    have hcontI : ContinuousOn f (Set.Icc m M) := hcont.mono hullsub
    have hinjI : Set.InjOn f (Set.Icc m M) := hinj.mono hullsub
    have ha₀hull : a₀ ∈ Set.Icc m M := by
      dsimp [m, M]
      exact ⟨min_le_right a a₀, le_trans hab₀.le (le_max_right b b₀)⟩
    have hb₀hull : b₀ ∈ Set.Icc m M := by
      dsimp [m, M]
      exact ⟨le_trans (min_le_right a a₀) hab₀.le, le_max_right b b₀⟩
    have hahull : a ∈ Set.Icc m M := by
      dsimp [m, M]
      exact ⟨min_le_left a a₀, le_trans hab.le (le_max_left b b₀)⟩
    have hbhull : b ∈ Set.Icc m M := by
      dsimp [m, M]
      exact ⟨le_trans (min_le_left a a₀) hab.le, le_max_left b b₀⟩
    rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (α := ℝ) (δ := ℝ) hmM hcontI hinjI with hmono | hanti
    · exfalso
      exact (not_lt_of_ge hle) (hmono ha₀hull hb₀hull hab₀)
    · exact hanti hahull hbhull hab

end Commons.Analysis.Order.ConnectedReal