import Mathlib
import Submission.Work.EKLContract.Defs

namespace Work.EKLC6Core

open MeasureTheory

/-- Union bound for the "frontier mass" functional: if every `frontier (P i)` is covered by the
union of the `frontier (U j)`, then the total `V η`-mass of the `P`-frontiers is at most the sum of
the individual `U`-bounds plus the slack `η` (the extra `1` covering the degenerate index range
`Fin (m+1)` versus `Fin m`). -/
theorem measure_iUnion_smul_frontier_le {m : ℕ} (μ : MeasureTheory.Measure Work.EKLContract.X3)
    {U : Fin m → Set Work.EKLContract.X3} {cU : Fin m → ℝ} (hcU : ∀ i, 0 < cU i)
    {η : ℝ} (hη : 0 < η)
    (hU : ∀ i, μ ((fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
        (Work.EKLContract.V η ×ˢ frontier (U i))) ≤ ENNReal.ofReal (cU i * η))
    (P : Fin (m + 1) → Set Work.EKLContract.X3)
    (hfr : ∀ i, frontier (P i) ⊆ ⋃ j, frontier (U j)) :
    μ (⋃ i, (fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
        (Work.EKLContract.V η ×ˢ frontier (P i)))
      ≤ ENNReal.ofReal ((∑ j, cU j + 1) * η) := by
  set M : Work.EKLContract.SL3 × Work.EKLContract.X3 → Work.EKLContract.X3 :=
    fun p => p.1 • p.2 with hM
  have hsub : (⋃ i, M '' (Work.EKLContract.V η ×ˢ frontier (P i)))
      ⊆ ⋃ j, M '' (Work.EKLContract.V η ×ˢ frontier (U j)) := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hx⟩ := hx
    rw [Set.mem_image] at hx
    obtain ⟨q, hq, hqx⟩ := hx
    rw [Set.mem_prod] at hq
    obtain ⟨hq1, hq2⟩ := hq
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hfr i hq2)
    rw [Set.mem_iUnion]
    refine ⟨j, ?_⟩
    rw [Set.mem_image]
    exact ⟨q, by rw [Set.mem_prod]; exact ⟨hq1, hj⟩, hqx⟩
  calc μ (⋃ i, M '' (Work.EKLContract.V η ×ˢ frontier (P i)))
      ≤ μ (⋃ j, M '' (Work.EKLContract.V η ×ˢ frontier (U j))) := measure_mono hsub
    _ ≤ ∑ j : Fin m, μ (M '' (Work.EKLContract.V η ×ˢ frontier (U j))) :=
        measure_iUnion_fintype_le μ _
    _ ≤ ∑ j : Fin m, ENNReal.ofReal (cU j * η) := Finset.sum_le_sum (fun j _ => hU j)
    _ = ENNReal.ofReal (∑ j : Fin m, cU j * η) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        exact fun j _ => le_of_lt (mul_pos (hcU j) hη)
    _ = ENNReal.ofReal ((∑ j : Fin m, cU j) * η) := by rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal ((∑ j : Fin m, cU j + 1) * η) :=
        ENNReal.ofReal_le_ofReal (by
          have h1 : (0:ℝ) ≤ ∑ j : Fin m, cU j := Finset.sum_nonneg (fun j _ => le_of_lt (hcU j))
          nlinarith)

end Work.EKLC6Core
