import Mathlib
import Submission.Work.Endgame.Defs

namespace Work.Endgame

/-- The complement of a point in a T1 space is open, hence its inclusion into the ambient
space is an open embedding. -/
theorem isOpenEmbedding_complSingleton {M : Type*} [TopologicalSpace M] [T1Space M] (p : M) :
    Topology.IsOpenEmbedding (Subtype.val : ({p}ᶜ : Set M) → M) := by
  exact (isClosed_singleton.isOpen_compl).isOpenEmbedding_subtypeVal

end Work.Endgame
