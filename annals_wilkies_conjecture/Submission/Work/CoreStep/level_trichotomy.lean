import Mathlib
import Submission.Work.CoreStep.level_eq_const_of_cover

namespace Work.CoreStep

open Filter Topology

theorem level_trichotomy {n m k : ℕ} {C : Set (Fin n → ℝ)}
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hk : 0 < k) (hCpre : IsPreconnected C)
    (hcont : ∀ j : Fin k, ContinuousOn (s j) C)
    (hdich : ∀ j j' : Fin k,
      (∃ x ∈ C, (s j x) (Fin.last m) = (s j' x) (Fin.last m)) →
      ∀ x ∈ C, (s j x) (Fin.last m) = (s j' x) (Fin.last m))
    (hbnd : ∀ j : Fin k, ∀ x ∈ C, |(s j x) (Fin.last m)| ≤ 1)
    (hsep : ∀ (j : Fin k) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      (∀ x ∈ C, (s j x) (Fin.last m) ≠ σ) ∨
      (∀ x ∈ C, ∃ j' : Fin k, (s j' x) (Fin.last m) = σ)) :
    ∀ j : Fin k,
      (∀ x ∈ C, (s j x) (Fin.last m) = 1) ∨
      (∀ x ∈ C, (s j x) (Fin.last m) = -1) ∨
      (∀ x ∈ C, |(s j x) (Fin.last m)| < 1) := by
  intro j
  -- If `s j` attains a value `σ ∈ {1, -1}` somewhere on `C`, then it is constantly `σ` on `C`.
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      (∃ x ∈ C, (s j x) (Fin.last m) = σ) →
      ∀ x ∈ C, (s j x) (Fin.last m) = σ := by
    intro σ hσ hatt
    -- `hsep` upgrades "`s j` attains `σ`" to "`σ` is attained at every point of `C`".
    have hcov : ∀ x ∈ C, ∃ j' : Fin k, (s j' x) (Fin.last m) = σ := by
      rcases hsep j σ hσ with h | h
      · exfalso
        obtain ⟨x, hx, hv⟩ := hatt
        exact h x hx hv
      · exact h
    -- Hence some level function is constantly `σ`; by `hdich` it agrees with `s j`.
    obtain ⟨j₀, hj₀⟩ := level_eq_const_of_cover hk hCpre hcont hdich hcov
    obtain ⟨x₀, hx₀, hx₀v⟩ := hatt
    intro x hx
    rw [hdich j j₀ ⟨x₀, hx₀, by rw [hx₀v, hj₀ x₀ hx₀]⟩ x hx]
    exact hj₀ x hx
  by_cases h1 : ∃ x ∈ C, (s j x) (Fin.last m) = 1
  · exact Or.inl (key 1 (Or.inl rfl) h1)
  · by_cases h2 : ∃ x ∈ C, (s j x) (Fin.last m) = -1
    · exact Or.inr (Or.inl (key (-1) (Or.inr rfl) h2))
    · -- `s j` avoids both `1` and `-1`, so `|s j| < 1` everywhere by `hbnd`.
      refine Or.inr (Or.inr ?_)
      intro x hx
      have hb : |(s j x) (Fin.last m)| ≤ 1 := hbnd j x hx
      refine lt_of_le_of_ne hb ?_
      intro habs
      rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp habs with h | h
      · exact h1 ⟨x, hx, h⟩
      · exact h2 ⟨x, hx, h⟩

end Work.CoreStep
