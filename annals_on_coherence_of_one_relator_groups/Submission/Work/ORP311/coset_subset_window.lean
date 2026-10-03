import Mathlib
import Submission.Work.ORP311.P311Defs

namespace Work.ORP311

theorem coset_subset_window {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} {m : ℕ} {j : ℤ} (h1 : -(m : ℤ) ≤ j) (h2 : j ≤ m) : Work.ORP311.coset N t j ⊆ Work.ORP311.window N t m := by
  rintro h ⟨n, rfl⟩
  exact ⟨n, j, h1, h2, rfl⟩

end Work.ORP311
