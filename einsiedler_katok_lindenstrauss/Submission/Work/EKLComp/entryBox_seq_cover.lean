import Mathlib
import Submission.Work.EKLContract.Defs

open Topology

namespace Work.EKLComp

/-- The whole of `SL₃(ℝ)` is covered by countably many entrywise `2δ`-boxes: enumerate a
countable dense subset of the ambient matrix space `Fin 3 → Fin 3 → ℝ` and take the boxes of
radius `δ` around its points. -/
theorem entryBox_seq_cover (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q : ℕ → Fin 3 → Fin 3 → ℝ,
      (Set.univ : Set Work.EKLContract.SL3) ⊆
        ⋃ n, {g : Work.EKLContract.SL3 | ∀ i j,
          |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - Q n i j| ≤ δ} := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense (Fin 3 → Fin 3 → ℝ)
  obtain ⟨Q, hQ⟩ := hsc.exists_eq_range hsd.nonempty
  refine ⟨Q, ?_⟩
  have hQd : DenseRange Q := by
    rw [DenseRange, ← hQ]; exact hsd
  intro g _
  rw [Set.mem_iUnion]
  have hopen : IsOpen {N : Fin 3 → Fin 3 → ℝ |
      ∀ i j, |N i j - (g : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ} := by
    have hset : {N : Fin 3 → Fin 3 → ℝ |
          ∀ i j, |N i j - (g : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ}
        = ⋂ i, ⋂ j, {N : Fin 3 → Fin 3 → ℝ |
            |N i j - (g : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ} := by
      ext N; simp
    rw [hset]
    apply isOpen_iInter_of_finite; intro i
    apply isOpen_iInter_of_finite; intro j
    exact isOpen_lt (by continuity) continuous_const
  have hne : Set.Nonempty {N : Fin 3 → Fin 3 → ℝ |
      ∀ i j, |N i j - (g : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ} :=
    ⟨(g : Matrix (Fin 3) (Fin 3) ℝ), by intro i j; simp [hδ]⟩
  obtain ⟨n, hn⟩ := hQd.exists_mem_open hopen hne
  exact ⟨n, fun i j => by rw [abs_sub_comm]; exact le_of_lt (hn i j)⟩

end Work.EKLComp
