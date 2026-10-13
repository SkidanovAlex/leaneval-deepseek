import Mathlib
import Submission.Work.WilG4c.FibreCoreDefs
import Submission.Work.WilG4c.FibrewiseClosure.FibClosureAux
import Submission.Work.WilG4c.FibrewiseClosure.fibreOf_fibrewiseClosure

namespace Work.WilG4c.FibrewiseClosure

theorem fibrewiseClosure_mem (S : WilkiesDesign.SOMin) (p N : ℕ) :
    ∃ K c : ℕ, ∀ (F D : ℕ) (Z : Set (Fin (p + N) → ℝ)),
      Z ∈ S.Ω F D (p + N) →
      Work.WilG4c.fibrewiseClosure Z ∈ S.Ω (F + K) (D + c) (p + N) ∧
      ∀ l : Fin p → ℝ,
        Work.WilG4c.fibreOf (Work.WilG4c.fibrewiseClosure Z) l
          = closure (Work.WilG4c.fibreOf Z l) := by
  obtain ⟨K, c, hK⟩ := Work.WilG4c.FibC.aux_mem S p N
  refine ⟨K, c, fun F D Z hZ => ⟨?_, ?_⟩⟩
  · rw [← Work.WilG4c.FibC.aux_eq]
    exact hK F D Z hZ
  · intro l
    exact fibreOf_fibrewiseClosure p N Z l

end Work.WilG4c.FibrewiseClosure
