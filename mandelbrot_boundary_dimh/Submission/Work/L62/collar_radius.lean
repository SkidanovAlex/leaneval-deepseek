import Mathlib

namespace Work.L62

/-- **Uniform collar around a finite family of points inside an open set.**
A finite set of points lying in an open set `DE` admits a positive radius `r` such that the
closed balls of radius `2 r` about all of them are still contained in `DE`. -/
theorem collar_radius {DE : Set ℂ} (hDE : IsOpen DE) {z : ℕ → ℂ} {J : ℕ}
    (hz : ∀ j : ℕ, 1 ≤ j → j ≤ J → z j ∈ DE) :
    ∃ r : ℝ, 0 < r ∧ (⋃ j ∈ Finset.Icc 1 J, Metric.closedBall (z j) (2 * r)) ⊆ DE := by
  -- The finite set of points is compact and contained in the open set `DE`.
  have hKsub : ((Finset.Icc 1 J).image z : Set ℂ) ⊆ DE := by
    intro x hx
    rw [Finset.mem_coe] at hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact hz j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  obtain ⟨δ, hδpos, hδsub⟩ :=
    ((Finset.Icc 1 J).image z).finite_toSet.isCompact.exists_cthickening_subset_open
      hDE hKsub
  refine ⟨δ / 4, by linarith, ?_⟩
  rintro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, hjmem, hx⟩ := hx
  have hzj : z j ∈ ((Finset.Icc 1 J).image z : Set ℂ) := by
    rw [Finset.mem_coe]; exact Finset.mem_image.mpr ⟨j, hjmem, rfl⟩
  have h2r : 2 * (δ / 4) = δ / 2 := by ring
  rw [h2r] at hx
  exact hδsub (Metric.cthickening_mono (by linarith) _
    (Metric.closedBall_subset_cthickening hzj (δ / 2) hx))

end Work.L62
