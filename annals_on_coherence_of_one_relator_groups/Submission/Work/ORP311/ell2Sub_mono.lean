import Mathlib
import Submission.Work.ORP311.LuckDim

namespace Work.ORP311

theorem ell2Sub_mono {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} {Z W : Set G} (h : Z ⊆ W) : Work.ORP311.ell2Sub (G := G) n Z ≤ Work.ORP311.ell2Sub (G := G) n W := by
  unfold ell2Sub
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro x ⟨g, hg, i, rfl⟩
  exact ⟨g, h hg, i, rfl⟩

end Work.ORP311
