import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.massOf_pos_iff

namespace Work.Geo.DualStretch

variable {n : ℕ}

/-- `minVal` is a lower bound for the values of `μ` on a nonempty finite set. -/
lemma minVal_le_of_mem {s : Finset (PL.E n)} {μ : PL.E n → ℝ} {v : PL.E n} (hv : v ∈ s) :
    Work.Geo.DualStretch.minVal s μ ≤ μ v := by
  rw [Work.Geo.DualStretch.minVal, dite_eq_left ⟨v, hv⟩]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem μ hv)

/-- `maxVal` is an upper bound for the values of `μ` on a finite set. -/
lemma le_maxVal_of_mem {s : Finset (PL.E n)} {μ : PL.E n → ℝ} {v : PL.E n} (hv : v ∈ s) :
    μ v ≤ Work.Geo.DualStretch.maxVal s μ := by
  rw [Work.Geo.DualStretch.maxVal, dite_eq_left ⟨v, hv⟩]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem μ hv)

/-- If two level sets `τ, τ' ⊆ s` both carry positive `massOf`-mass, then they are comparable by
inclusion: positivity forces every element of `τ` to have strictly larger `μ`-value than every
element of `s \ τ` (and similarly for `τ'`), and two such "top slices" of a finite set must be
nested. -/
theorem massOf_chain {n : ℕ} {s τ τ' : Finset (PL.E n)} {μ : PL.E n → ℝ} (hτ : τ ⊆ s) (hτ' : τ' ⊆ s)
    (h : 0 < Work.Geo.DualStretch.massOf s μ τ) (h' : 0 < Work.Geo.DualStretch.massOf s μ τ') :
    τ ⊆ τ' ∨ τ' ⊆ τ := by
  rw [Work.Geo.DualStretch.massOf_pos_iff hτ] at h
  rw [Work.Geo.DualStretch.massOf_pos_iff hτ'] at h'
  by_contra hc
  rw [not_or] at hc
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨v, hvτ, hvτ'⟩ := Finset.not_subset.mp hc1
  obtain ⟨w, hwτ', hwτ⟩ := Finset.not_subset.mp hc2
  have hv : μ v ≤ Work.Geo.DualStretch.maxVal (s \ τ') μ :=
    le_maxVal_of_mem (Finset.mem_sdiff.mpr ⟨hτ hvτ, hvτ'⟩)
  have hw : μ w ≤ Work.Geo.DualStretch.maxVal (s \ τ) μ :=
    le_maxVal_of_mem (Finset.mem_sdiff.mpr ⟨hτ' hwτ', hwτ⟩)
  have hv' : Work.Geo.DualStretch.minVal τ' μ ≤ μ w := minVal_le_of_mem hwτ'
  have hw' : Work.Geo.DualStretch.minVal τ μ ≤ μ v := minVal_le_of_mem hvτ
  linarith [h.2, h'.2]

end Work.Geo.DualStretch
