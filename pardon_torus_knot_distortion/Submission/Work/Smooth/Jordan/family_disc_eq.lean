import Mathlib
import Submission.Work.Smooth.Jordan.Family

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Jordan

noncomputable section

theorem family_disc_eq {A : Set R3} {ι : Type} [Fintype ι] {c : ι → ℝ → R3}
    (h : FamilyDiscs A ι c) (i : ι) :
    Set.range (h.disc i) = h.disc i '' {z : Disc | ‖(z : ℂ)‖ < 1} ∪ Set.range (c i) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    by_cases hz : ‖(z : ℂ)‖ < 1
    · exact Or.inl ⟨z, hz, rfl⟩
    · have hle : ‖(z : ℂ)‖ ≤ 1 := by
        have := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
      have hz1 : ‖(z : ℂ)‖ = 1 := le_antisymm hle (not_lt.mp hz)
      obtain ⟨θ, hθ⟩ := exists_circlePoint_eq z hz1
      exact Or.inr ⟨θ, by rw [← hθ, h.disc_boundary i θ]⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨θ, rfl⟩)
    · exact ⟨z, rfl⟩
    · exact ⟨circlePoint θ, h.disc_boundary i θ⟩

end

end Work.Smooth.Jordan
