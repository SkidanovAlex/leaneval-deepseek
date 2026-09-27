import Mathlib
import Submission.Work.EKLC6Route.Defs

namespace Work.EKLC6Route

/-- The grid-cell fibres `{k | gridIdx ρ ℓ k = d}` cover all of `SL3`: every `k` lies in
the cell indexed by `gridIdx ρ ℓ k`. -/
theorem iUnion_gridIdx_eq_univ (ρ : ℝ) (ℓ : ℕ) :
    (⋃ d : Fin 3 → Fin 3 → ℤ, {k : Work.EKLContract.SL3 | gridIdx ρ ℓ k = d}) = Set.univ := by
  ext k
  simp

/-- Splitting `θ ⁻¹' C` along the grid cells refines nothing: the union over all grid cells
of `W ∩ θ ⁻¹' (C ∩ {gridIdx = d})` is exactly `W ∩ θ ⁻¹' C`. -/
theorem iUnion_grid_cell_eq (ρ : ℝ) (ℓ : ℕ) (θ : Work.EKLContract.X3 → Work.EKLContract.SL3)
    (W : Set Work.EKLContract.X3) (C : Set Work.EKLContract.SL3) :
    (⋃ d : Fin 3 → Fin 3 → ℤ,
        W ∩ θ ⁻¹' (C ∩ {k : Work.EKLContract.SL3 | gridIdx ρ ℓ k = d}))
      = W ∩ θ ⁻¹' C := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨d, hW, hC, _⟩
    exact ⟨hW, hC⟩
  · intro hx
    rcases hx with ⟨hW, hC⟩
    exact Set.mem_iUnion.mpr ⟨gridIdx ρ ℓ (θ x), hW, hC, rfl⟩

theorem exists_grid_cell_pos {μ : MeasureTheory.Measure Work.EKLContract.X3} {ρ : ℝ} {ℓ : ℕ} {θ : Work.EKLContract.X3 → Work.EKLContract.SL3} {W : Set Work.EKLContract.X3} {C : Set Work.EKLContract.SL3} (hpos : 0 < μ (W ∩ θ ⁻¹' C)) : ∃ d : Fin 3 → Fin 3 → ℤ, 0 < μ (W ∩ θ ⁻¹' (C ∩ {k : Work.EKLContract.SL3 | Work.EKLC6Route.gridIdx ρ ℓ k = d})) := by
  by_contra h
  push Not at h
  have hzero : ∀ d : Fin 3 → Fin 3 → ℤ,
      μ (W ∩ θ ⁻¹' (C ∩ {k : Work.EKLContract.SL3 | gridIdx ρ ℓ k = d})) = 0 := by
    intro d
    exact le_antisymm (h d) bot_le
  have hsplit : (⋃ d : Fin 3 → Fin 3 → ℤ,
        W ∩ θ ⁻¹' (C ∩ {k : Work.EKLContract.SL3 | gridIdx ρ ℓ k = d})) = W ∩ θ ⁻¹' C :=
    iUnion_grid_cell_eq ρ ℓ θ W C
  have hnull : μ (W ∩ θ ⁻¹' C) = 0 := by
    rw [← hsplit]
    exact MeasureTheory.measure_iUnion_null hzero
  rw [hnull] at hpos
  exact lt_irrefl 0 hpos

end Work.EKLC6Route
