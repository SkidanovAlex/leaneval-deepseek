import Mathlib
import Submission.Work.HornSC.Cells

namespace Work.HornSC.DilInterior

open Set Work.HornSC

/-- The open `3 × 3` square centred on the closed cell `p`: one unit of margin on every side. -/
private def openSquare (p : ℤ × ℤ) : Set ℂ :=
  {w : ℂ | (p.1 : ℝ) - 1 < w.re ∧ w.re < (p.1 : ℝ) + 2 ∧
          (p.2 : ℝ) - 1 < w.im ∧ w.im < (p.2 : ℝ) + 2}

private lemma isOpen_openSquare (p : ℤ × ℤ) : IsOpen (openSquare p) := by
  have h1 : IsOpen {w : ℂ | (p.1 : ℝ) - 1 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {w : ℂ | w.re < (p.1 : ℝ) + 2} :=
    isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {w : ℂ | (p.2 : ℝ) - 1 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have h4 : IsOpen {w : ℂ | w.im < (p.2 : ℝ) + 2} :=
    isOpen_lt Complex.continuous_im continuous_const
  have h := h1.inter (h2.inter (h3.inter h4))
  convert h using 1
  ext w
  simp only [openSquare, Set.mem_inter_iff, Set.mem_ofPred_eq]

private lemma openSquare_subset_cellUnion_dil3 {A : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ A) :
    openSquare p ⊆ cellUnion (dil3 A) := by
  intro w hw
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  have hle1 : ((⌊w.re⌋ : ℤ) : ℝ) ≤ w.re := Int.floor_le w.re
  have hlt1 : w.re < ((⌊w.re⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one w.re
  have hle2 : ((⌊w.im⌋ : ℤ) : ℝ) ≤ w.im := Int.floor_le w.im
  have hlt2 : w.im < ((⌊w.im⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one w.im
  have hq1 : |⌊w.re⌋ - p.1| ≤ 1 := by
    have hup : ⌊w.re⌋ ≤ p.1 + 1 := by
      have h : ((⌊w.re⌋ : ℤ) : ℝ) < ((p.1 + 2 : ℤ) : ℝ) := by push_cast; linarith
      have h' : ⌊w.re⌋ < p.1 + 2 := Int.cast_lt.mp h
      omega
    have hlo : p.1 - 1 ≤ ⌊w.re⌋ := by
      have h : ((p.1 - 2 : ℤ) : ℝ) < ((⌊w.re⌋ : ℤ) : ℝ) := by push_cast; linarith
      have h' : p.1 - 2 < ⌊w.re⌋ := Int.cast_lt.mp h
      omega
    rw [abs_le]; omega
  have hq2 : |⌊w.im⌋ - p.2| ≤ 1 := by
    have hup : ⌊w.im⌋ ≤ p.2 + 1 := by
      have h : ((⌊w.im⌋ : ℤ) : ℝ) < ((p.2 + 2 : ℤ) : ℝ) := by push_cast; linarith
      have h' : ⌊w.im⌋ < p.2 + 2 := Int.cast_lt.mp h
      omega
    have hlo : p.2 - 1 ≤ ⌊w.im⌋ := by
      have h : ((p.2 - 2 : ℤ) : ℝ) < ((⌊w.im⌋ : ℤ) : ℝ) := by push_cast; linarith
      have h' : p.2 - 2 < ⌊w.im⌋ := Int.cast_lt.mp h
      omega
    rw [abs_le]; omega
  have hq : (⌊w.re⌋, ⌊w.im⌋) ∈ dil3 A := mem_dil3.mpr ⟨p, hp, hq1, hq2⟩
  refine Set.mem_iUnion₂.mpr ⟨(⌊w.re⌋, ⌊w.im⌋), hq, ?_⟩
  rw [mem_cell]
  exact ⟨Int.floor_le w.re, le_of_lt (Int.lt_floor_add_one w.re), Int.floor_le w.im,
    le_of_lt (Int.lt_floor_add_one w.im)⟩

/-- Every cell of `A` is contained in the interior of the union of the `3 × 3` dilation of `A`. -/
private lemma cell_subset_interior_cellUnion_dil3 {A : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ A) :
    cell p ⊆ interior (cellUnion (dil3 A)) := by
  have hsub : openSquare p ⊆ cellUnion (dil3 A) := openSquare_subset_cellUnion_dil3 hp
  have hcell : cell p ⊆ openSquare p := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := mem_cell.mp hw
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  exact subset_trans hcell (interior_maximal hsub (isOpen_openSquare p))

theorem cellUnion_subset_interior_dil3 (A : Finset (ℤ × ℤ)) :
    cellUnion A ⊆ interior (cellUnion (dil3 A)) := by
  intro z hz
  obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
  exact cell_subset_interior_cellUnion_dil3 hp hzp

end Work.HornSC.DilInterior
