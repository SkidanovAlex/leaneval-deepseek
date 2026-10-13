import Mathlib
import Submission.Work.WilC4aA.Defs

namespace Work.WilC4aA

/-- `0` is an accumulation point of the image of `S` under the coordinate map `z ↦ z 0`. -/
lemma zero_mem_closure_coord_image {m : ℕ} {S : Set (Fin (m + 1) → ℝ)}
    (h : ∀ δ > (0 : ℝ), ∃ z ∈ S, z 0 ∈ Set.Ioo (0 : ℝ) δ) :
    (0 : ℝ) ∈ closure ((fun z : Fin (m + 1) → ℝ => z 0) '' S) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hzS, hz⟩ := h ε hε
  refine ⟨z 0, ⟨z, hzS, rfl⟩, ?_⟩
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hz.1]
  exact hz.2

theorem accum_closure_point {m : ℕ} {S : Set (Fin (m + 1) → ℝ)}
    (hb : Bornology.IsBounded S) (h : ∀ δ > (0 : ℝ), ∃ z ∈ S, z 0 ∈ Set.Ioo (0 : ℝ) δ) :
    ∃ q ∈ closure S, q 0 = 0 := by
  let f : (Fin (m + 1) → ℝ) → ℝ := fun z => z 0
  have hcont : Continuous f := continuous_apply 0
  -- `closure S` is compact (bounded in finite dimension), hence so is its image under `f`.
  have hc : IsCompact (closure S) := hb.isCompact_closure
  have hclosed : IsClosed (f '' closure S) := (hc.image hcont).isClosed
  -- `0` lies in the closure of `f '' S`, which is contained in the closed set `f '' closure S`.
  have h0 : (0 : ℝ) ∈ closure (f '' S) := zero_mem_closure_coord_image h
  have hsub : f '' S ⊆ f '' closure S := Set.image_mono subset_closure
  have hmem : (0 : ℝ) ∈ f '' closure S := (hclosed.closure_subset_iff.mpr hsub) h0
  obtain ⟨q, hq, hq0⟩ := hmem
  exact ⟨q, hq, hq0⟩

end Work.WilC4aA
