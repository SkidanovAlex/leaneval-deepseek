import Mathlib

namespace Work.WilG5.Cell

theorem contOn_abs_lt {n : ℕ} {f : (Fin n → ℝ) → ℝ} {C : Set (Fin n → ℝ)}
    (hf : ContinuousOn f C) {y0 : Fin n → ℝ} (hy0 : y0 ∈ C) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ C, (∀ i, |y' i - y0 i| < δ) → |f y' - f y0| < η := by
  obtain ⟨δ, hδ, h⟩ := (Metric.tendsto_nhdsWithin_nhds.mp (hf.continuousWithinAt hy0)) η hη
  refine ⟨δ, hδ, fun y' hy' hyy => ?_⟩
  rw [← Real.dist_eq]
  refine h hy' ?_
  rw [dist_pi_lt_iff hδ]
  intro i
  rw [Real.dist_eq]
  exact hyy i

end Work.WilG5.Cell
