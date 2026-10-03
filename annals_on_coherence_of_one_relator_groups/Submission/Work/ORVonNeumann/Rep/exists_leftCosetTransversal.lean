import Mathlib
import Submission.Work.ORVonNeumann.Rep.delta1_separating

namespace Work.ORVonNeumann.Rep

theorem exists_leftCosetTransversal {G : Type*} [Group G] (H : Subgroup G) : ∃ Q : Set G, (∀ g : G, ∃! p : ↥H × Q, (p.1 : G) * p.2 = g) := by
  obtain ⟨Q, hQ, -⟩ := H.exists_isComplement_right (1 : G)
  exact ⟨Q, fun g => hQ.existsUnique g⟩

end Work.ORVonNeumann.Rep
