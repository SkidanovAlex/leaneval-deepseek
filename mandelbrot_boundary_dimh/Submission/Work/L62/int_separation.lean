import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.L62

/-- **Separation from `ℤ` in `ℂ`.**  A complex number which is not an integer has a positive
distance from `ℤ`. -/
theorem int_separation {x : ℂ} (hx : ∀ k : ℤ, x ≠ (k : ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℤ, δ ≤ ‖x - (k : ℂ)‖ := by
  -- `ℤ ↪ ℂ` is a closed embedding, so its range is closed; the conclusion then follows from
  -- the metric characterisation of the closure.
  have hS : IsClosed (Set.range (fun k : ℤ => (k : ℂ))) :=
    Complex.isClosedEmbedding_intCast.isClosed_range
  have hxS : x ∉ Set.range (fun k : ℤ => (k : ℂ)) := by
    rintro ⟨k, hk⟩
    exact hx k hk.symm
  have hnotcl : x ∉ closure (Set.range (fun k : ℤ => (k : ℂ))) := by
    rwa [hS.closure_eq]
  rw [Metric.mem_closure_iff] at hnotcl
  simp only [not_forall, not_exists] at hnotcl
  obtain ⟨ε, hε, hε'⟩ := hnotcl
  refine ⟨ε, hε, fun k => ?_⟩
  have h1 : ¬ dist x ((k : ℂ)) < ε := fun hlt => hε' (k : ℂ) ⟨⟨k, rfl⟩, hlt⟩
  have h2 : ε ≤ dist x ((k : ℂ)) := le_of_not_gt h1
  rwa [dist_eq_norm] at h2

end Work.L62
