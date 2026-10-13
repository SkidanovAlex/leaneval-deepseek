import Mathlib
import Submission.Work.Wilkies.Defs

namespace Work.WilkiesI

theorem InjOnCoordSection {μ n : ℕ} (e : Fin μ ↪ Fin n) {U : Set (Fin μ → ℝ)} {ψ : (Fin μ → ℝ) → (Fin n → ℝ)} (hsec : ∀ t ∈ U, ψ t ∘ e = t) : Set.InjOn ψ U := by
  intro a ha b hb hab
  calc a = ψ a ∘ e := (hsec a ha).symm
    _ = ψ b ∘ e := by rw [hab]
    _ = b := hsec b hb

end Work.WilkiesI
