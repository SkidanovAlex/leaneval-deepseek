import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs

namespace Work.ORHughesFree.NaturalExtension

/-- A bounded real-valued sequence that converges to `l` has ultralimit `l` along any ultrafilter
containing the cofinite filter. -/
theorem blim_of_tendsto (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop)
    {f : ℕ → ℝ} {l M : ℝ} (hf : ∀ i, |f i| ≤ M)
    (h : Filter.Tendsto f Filter.atTop (nhds l)) : blim ω f = l := by
  set S : Set ℝ := {r : ℝ | {i | r ≤ f i} ∈ ω} with hS
  have hblim : blim ω f = sSup S := rfl
  rw [hblim]
  -- For `r > l`, the set `{i | r ≤ f i}` lies below a tail, so it is not in `ω`.
  have hnotmem : ∀ r : ℝ, l < r → {i | r ≤ f i} ∉ ω := by
    intro r hr hmem
    have hε : 0 < (r - l) / 2 := by linarith
    have hpre : f ⁻¹' Metric.ball l ((r - l) / 2) ∈ Filter.atTop := by
      have hb := h (Metric.ball_mem_nhds l hε)
      rwa [Filter.mem_map] at hb
    have hsub : f ⁻¹' Metric.ball l ((r - l) / 2) ⊆ {i | r ≤ f i}ᶜ := by
      intro i hi
      rw [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
      rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hi
      have h2 := (abs_lt.mp hi).2
      linarith
    have hcompl : {i | r ≤ f i}ᶜ ∈ (ω : Filter ℕ) := hω (Filter.mem_of_superset hpre hsub)
    have hmem' : {i | r ≤ f i} ∈ (ω : Filter ℕ) := hmem
    have hinter : ({i | r ≤ f i} ∩ {i | r ≤ f i}ᶜ) ∈ (ω : Filter ℕ) :=
      Filter.inter_mem hmem' hcompl
    have hemp : (∅ : Set ℕ) ∈ (ω : Filter ℕ) := by
      rw [← Set.inter_compl_self {i | r ≤ f i}]
      exact hinter
    exact Ultrafilter.empty_notMem hemp
  -- For `r < l`, the set `{i | r ≤ f i}` contains a tail, so it is in `ω`.
  have hmem_of_lt : ∀ r : ℝ, r < l → r ∈ S := by
    intro r hr
    rw [hS]
    simp only [Set.mem_ofPred_eq]
    have hε : 0 < (l - r) / 2 := by linarith
    have hpre : f ⁻¹' Metric.ball l ((l - r) / 2) ∈ Filter.atTop := by
      have hb := h (Metric.ball_mem_nhds l hε)
      rwa [Filter.mem_map] at hb
    have hsub : f ⁻¹' Metric.ball l ((l - r) / 2) ⊆ {i | r ≤ f i} := by
      intro i hi
      rw [Set.mem_ofPred_eq]
      rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hi
      have h1 := (abs_lt.mp hi).1
      linarith
    exact hω (Filter.mem_of_superset hpre hsub)
  -- `l` is an upper bound of `S`.
  have hub : ∀ r ∈ S, r ≤ l := by
    intro r hr
    by_contra hlt
    rw [not_le] at hlt
    rw [hS] at hr
    simp only [Set.mem_ofPred_eq] at hr
    exact hnotmem r hlt hr
  have hbdd : BddAbove S := ⟨l, fun x hx => hub x hx⟩
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨l - 1, hmem_of_lt (l - 1) (by linarith)⟩ ?_
    intro r hr
    exact hub r hr
  · by_contra hcon
    rw [not_le] at hcon
    have hr : (sSup S + l) / 2 < l := by linarith
    have hmem := hmem_of_lt _ hr
    have hle := le_csSup hbdd hmem
    linarith

end Work.ORHughesFree.NaturalExtension
