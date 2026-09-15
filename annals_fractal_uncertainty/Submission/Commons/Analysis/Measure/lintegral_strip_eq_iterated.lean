import Mathlib
import Submission.Commons.Analysis.Measure.integral_strip_eq_iterated

namespace Commons.Analysis.Measure

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem lintegral_strip_eq_iterated {d : ℕ} {g : (Fin d → ℂ) → ENNReal}
    (hg : AEMeasurable g (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) {Q : ℝ} :
    ∫⁻ z in {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ Q}, g z
      = ∫⁻ y in Set.pi Set.univ (fun _ : Fin d => Set.Icc (-Q) Q),
          ∫⁻ x : Fin d → ℝ, g (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) := by
  classical
  set B : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ : Fin d => Set.Icc (-Q) Q) with hB
  set S : Set (Fin d → ℂ) := {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ Q} with hS
  have hmp : MeasurePreserving (stripEquiv d) := stripEquiv_measurePreserving d
  have hBmeas : MeasurableSet B := by
    rw [hB]
    exact MeasurableSet.univ_pi (fun _ => isClosed_Icc.measurableSet)
  have hUxB : MeasurableSet (Set.univ ×ˢ B) :=
    MeasurableSet.prod (s := (Set.univ : Set (Fin d → ℝ))) (t := B) MeasurableSet.univ hBmeas
  have hpre : (stripEquiv d) ⁻¹' S = Set.univ ×ˢ B := by
    ext p
    simp only [Set.mem_preimage, hS, hB, Set.mem_prod, Set.mem_pi, Set.mem_Icc,
      Set.mem_ofPred_eq, Set.mem_univ, true_implies, true_and]
    have him : ∀ i, ((stripEquiv d) p i).im = p.2 i := by
      intro i
      rw [stripEquiv_apply d p.1 p.2]
      simp
    constructor
    · intro h i
      have := abs_le.mp (h i)
      rwa [him i] at this
    · intro h i
      have := abs_le.mpr (h i)
      simpa [him i] using this
  set F : (Fin d → ℝ) × (Fin d → ℝ) → ENNReal := fun p => g (stripEquiv d p) with hF
  set G : (Fin d → ℝ) × (Fin d → ℝ) → ENNReal := (Set.univ ×ˢ B).indicator F with hG
  have hFAE : AEMeasurable F (volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := by
    have h := (hmp.aemeasurable_comp_iff
      (MeasurableEquiv.measurableEmbedding (stripEquiv d))).mpr hg
    exact h
  have hGAE : AEMeasurable G (volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := by
    rw [hG]; exact hFAE.indicator hUxB
  have hrestrict : (volume : Measure (Fin d → ℂ)).restrict S
      = Measure.map (stripEquiv d)
          ((volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))).restrict ((stripEquiv d) ⁻¹' S)) := by
    have h1 : (Measure.map (stripEquiv d)
        (volume : Measure ((Fin d → ℝ) × (Fin d → ℝ)))).restrict S
        = Measure.map (stripEquiv d)
            ((volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))).restrict ((stripEquiv d) ⁻¹' S)) :=
      MeasurableEquiv.restrict_map (stripEquiv d)
        (volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))) S
    rw [hmp.map_eq] at h1
    exact h1
  have key : ∫⁻ z in S, g z
      = ∫⁻ p, F p ∂((volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))).restrict (Set.univ ×ˢ B)) := by
    have h2 : ∫⁻ z in S, g z
        = ∫⁻ z, g z ∂Measure.map (stripEquiv d)
            ((volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))).restrict ((stripEquiv d) ⁻¹' S)) := by
      rw [← hrestrict]
    rw [h2, lintegral_map_equiv g (stripEquiv d), hpre]
  have hGF : ∫⁻ p, G p ∂(volume : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
      = ∫⁻ p, F p ∂((volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))).restrict (Set.univ ×ˢ B)) := by
    rw [hG]
    exact lintegral_indicator hUxB F
  have step1 : ∫⁻ z in S, g z
      = ∫⁻ p, G p ∂(volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := key.trans hGF.symm
  have step2 : ∫⁻ p, G p ∂(volume : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
      = ∫⁻ y, ∫⁻ x, G (x, y) ∂volume ∂volume := by
    have h := lintegral_prod_symm (μ := (volume : Measure (Fin d → ℝ)))
      (ν := (volume : Measure (Fin d → ℝ))) G hGAE
    exact h
  have step3 : ∫⁻ y, ∫⁻ x, G (x, y) ∂volume ∂volume
      = ∫⁻ y, B.indicator (fun y' => ∫⁻ x, F (x, y')) y ∂volume := by
    refine lintegral_congr (fun y => ?_)
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy]
      refine lintegral_congr (fun x => ?_)
      rw [hG]
      exact indicator_of_mem (s := Set.univ ×ˢ B) ⟨mem_univ x, hy⟩ F
    · rw [indicator_of_notMem hy, hG]
      have hz : (fun x : Fin d → ℝ => (Set.univ ×ˢ B).indicator F (x, y)) = fun _ => 0 := by
        funext x
        rw [indicator_of_notMem (s := Set.univ ×ˢ B)]
        exact fun h => hy h.2
      rw [hz, lintegral_zero]
  have step4 : ∫⁻ y, B.indicator (fun y' => ∫⁻ x, F (x, y')) y ∂volume
      = ∫⁻ y in B, ∫⁻ x, F (x, y) ∂volume :=
    lintegral_indicator hBmeas (fun y' => ∫⁻ x, F (x, y'))
  have step5 : ∫⁻ y in B, ∫⁻ x, F (x, y) ∂volume
      = ∫⁻ y in B, ∫⁻ x : Fin d → ℝ,
          g (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) := by
    refine lintegral_congr (fun y => ?_)
    refine lintegral_congr (fun x => ?_)
    exact congr_arg g (stripEquiv_apply d x y)
  rw [step1, step2, step3, step4, step5]

end

end Commons.Analysis.Measure
