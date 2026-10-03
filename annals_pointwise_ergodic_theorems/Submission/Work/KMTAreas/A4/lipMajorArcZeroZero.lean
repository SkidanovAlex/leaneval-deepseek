import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory
open Work.Analysis.IonescuWainger

/-- The set `(ℚ/ℤ)_{≤0}` of Ionescu–Wainger arithmetic frequencies of height at most `2^0 = 1`
contains the trivial frequency `0` (indeed `iwP ρ 0 = {1}`, so `iwArithFreqs ρ 0 = {0}`). -/
lemma mem_iwArithFreqs_zero (ρ : ℝ) : (0 : FreqCircle) ∈ iwArithFreqs ρ 0 := by
  rw [iwArithFreqs]
  refine Finset.mem_biUnion.mpr ⟨1, ?_, ?_⟩
  · rw [iwP]; simp
  · refine Finset.mem_image.mpr ⟨0, ?_, ?_⟩
    · simp
    · simp

/-- The projection `ℝ → ℝ/ℤ` restricted to `[-1, 0]` (hence to the interval `ℝ_{≤0} = [-1,1]`
containing it) is already surjective. -/
lemma surjOn_Icc_neg_one_zero :
    ((↑) : ℝ → FreqCircle) '' Set.Icc (-1 : ℝ) 0 = Set.univ := by
  have h := AddCircle.coe_image_Icc_eq (p := (1 : ℝ)) (a := (-1 : ℝ))
  simpa using h

/-- **The major arcs at `l = k = 0` are everything.**  Indeed `iwArithFreqs ρ 0 = {0}` and
`realFreqInterval 0 = [-1,1]`, and every class in `ℝ/ℤ` has a representative in `[-1,0] ⊆ [-1,1]`. -/
theorem lipMajorArcZeroZero {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Work.Analysis.InverseTheory.majorArc ρ 0 0 = Set.univ := by
  refine Set.eq_univ_of_forall fun γ => ?_
  rw [mem_majorArc]
  obtain ⟨θ, hθ, hθγ⟩ : ∃ θ ∈ Set.Icc (-1 : ℝ) 0, ((θ : ℝ) : FreqCircle) = γ := by
    have h : γ ∈ ((↑) : ℝ → FreqCircle) '' Set.Icc (-1 : ℝ) 0 := by
      rw [surjOn_Icc_neg_one_zero]; exact Set.mem_univ γ
    exact h
  refine ⟨0, mem_iwArithFreqs_zero ρ, θ, ?_, ?_⟩
  · rw [mem_realFreqInterval]
    constructor <;> linarith [hθ.1, hθ.2]
  · rw [zero_add]; exact hθγ.symm

end Work.KMTAreas.A4
