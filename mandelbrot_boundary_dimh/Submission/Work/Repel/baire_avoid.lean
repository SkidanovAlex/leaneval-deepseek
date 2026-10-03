import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Repel

/-- Baire category in the plane: an open nonempty set meets the complement of a
countable union of closed sets with empty interior. -/
theorem baire_avoid {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {B : ℕ → Set ℂ} (hclosed : ∀ i, IsClosed (B i)) (hint : ∀ i, interior (B i) = ∅) :
    ∃ u ∈ U, ∀ i, u ∉ B i := by
  -- Each `(B i)ᶜ` is open and dense, so by Baire category their countable
  -- intersection is dense in ℂ.
  have hdense : Dense (⋂ i, (B i)ᶜ) := by
    apply dense_iInter_of_isOpen
    · intro i; exact (hclosed i).isOpen_compl
    · intro i
      simp [Dense, closure_compl, hint i]
  -- A dense set meets every nonempty open set.
  rcases hdense.exists_mem_open hU hUne with ⟨u, hu, huU⟩
  refine ⟨u, huU, ?_⟩
  intro i h
  exact (Set.mem_iInter.mp hu i) h

end Work.Repel
