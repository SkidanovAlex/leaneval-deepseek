import Mathlib
import Submission.Work.WilG4c.exists_nearmax_of_bdd

namespace Work.WilG4c

theorem ExistsNearmaxBox {n : ℕ} (D : (Fin n → ℝ) → ℝ) (K : ℝ) (y₀ : Fin n → ℝ)
    (hy₀ : ∀ i, y₀ i ∈ Set.Ioo (0 : ℝ) 1) (hD₀ : |D y₀| ≤ K) :
    ∃ yc : Fin n → ℝ,
      (∀ i, yc i ∈ Set.Ioo (0 : ℝ) 1) ∧
      |D yc| ≤ K ∧
      ∀ y' : Fin n → ℝ, (∀ i, y' i ∈ Set.Ioo (0 : ℝ) 1) → |D y'| ≤ K →
        |D y'| ≤ 2 * |D yc| := by
  -- Work on the set of admissible points, whose values are bounded by `K`.
  obtain ⟨yc, hyc, hmax⟩ :=
    exists_nearmax_of_bdd
      (S := {y : Fin n → ℝ | (∀ i, y i ∈ Set.Ioo (0 : ℝ) 1) ∧ |D y| ≤ K})
      ⟨y₀, hy₀, hD₀⟩ D (by
        refine ⟨K, ?_⟩
        rintro z ⟨y, ⟨-, hyK⟩, rfl⟩
        exact hyK)
  exact ⟨yc, hyc.1, hyc.2, fun y' hy' hy'K => hmax y' ⟨hy', hy'K⟩⟩

end Work.WilG4c
