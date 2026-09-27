import Mathlib
import Submission.Work.Mostow.LinAlgMatrixIneqAux

namespace Work.Mostow

/-- Any point of the box `Kset n δ` (`δ > 0`, `n ≥ 2`) has all its coordinates
strictly below `1`.

Indeed `y ∈ Kset n δ` means `δ ≤ y i` for every `i` and `∑ i, y i = 1`; with at
least two coordinates and all of them `≥ δ > 0`, the remaining coordinates sum
to `1 - y k > 0`. -/
theorem one_sub_pos_of_mem_Kset {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hn : 2 ≤ n)
    {y : Fin n → ℝ} (hy : y ∈ Kset n δ) (k : Fin n) : 0 < 1 - y k := by
  obtain ⟨hge, hsum⟩ := hy
  obtain ⟨j, hjk⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n)
    (by simp only [Fintype.card_fin]; omega : 1 < Fintype.card (Fin n)) k
  have hsplit : (∑ i ∈ (Finset.univ : Finset (Fin n)).erase k, y i) = 1 - y k := by
    have h1 := Finset.sum_erase_add (s := Finset.univ) (f := y) (Finset.mem_univ k)
    linarith
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)).erase k, 0 ≤ y i := by
    intro i _; linarith [hge i]
  have hjmem : j ∈ (Finset.univ : Finset (Fin n)).erase k := by
    simp [Finset.mem_erase, hjk]
  have hle : y j ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)).erase k, y i :=
    Finset.single_le_sum hnonneg hjmem
  have : 0 < ∑ i ∈ (Finset.univ : Finset (Fin n)).erase k, y i := by
    have := hge j; linarith
  linarith

end Work.Mostow
