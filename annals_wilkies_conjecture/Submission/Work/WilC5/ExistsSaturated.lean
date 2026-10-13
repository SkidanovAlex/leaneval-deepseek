import Mathlib
import Submission.Work.WilC5.Saturation
import Submission.Work.WilC5.SatFinal

namespace Work.WilC5

theorem ExistsSaturated {L : FirstOrder.Language.{0, 0}} (M : Type) [L.Structure M]
    (κ : Cardinal.{0}) :
    ∃ (N : Type) (instN : L.Structure N),
      ∃ (f : @FirstOrder.Language.ElementaryEmbedding L M N _ instN),
        @Work.WilC5.IsSaturated L N instN κ := by
  by_cases h : Nonempty M
  · exact SatExists L M κ h
  · refine ⟨M, inferInstance,
      FirstOrder.Language.ElementaryEmbedding.ofModelsElementaryDiagram L M M, ?_⟩
    intro A hA p hp
    exfalso
    obtain ⟨x, -⟩ := hp ∅ (by simp)
    exact h ⟨x 0⟩

end Work.WilC5
