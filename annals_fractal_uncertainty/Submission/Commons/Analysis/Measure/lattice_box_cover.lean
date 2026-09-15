import Mathlib

namespace Commons.Analysis.Measure

open MeasureTheory Metric Set

/-- The unit boxes `2n + γ + 1 + [-1,1]^d` of the `2ℤ^d` lattice cover `ℝ^d`. -/
theorem lattice_box_cover {d : ℕ} (γ : Fin d → ℝ) :
    ⋃ n : Fin d → ℤ, {x : Fin d → ℝ | ∀ i : Fin d, |x i - (2 * (n i : ℝ) + γ i + 1)| ≤ 1}
      = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  simp only [mem_iUnion, mem_setOf_eq]
  refine ⟨fun i => ⌊(x i - γ i) / 2⌋, fun i => ?_⟩
  rw [abs_le]
  constructor
  · have h := Int.floor_le ((x i - γ i) / 2)
    linarith
  · have h := Int.lt_floor_add_one ((x i - γ i) / 2)
    linarith

end Commons.Analysis.Measure
