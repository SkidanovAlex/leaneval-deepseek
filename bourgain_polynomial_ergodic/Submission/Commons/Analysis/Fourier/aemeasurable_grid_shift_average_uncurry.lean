import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.Analysis.Fourier

open MeasureTheory

/-- The parameterized Bochner integral of an integrable function over `Set.Ioc (a p) (b p)`
is a.e. measurable in `p`, for measurable `a`, `b`. -/
lemma aemeasurable_setIntegral_Ioc_volume (g : ℝ → ℂ)
    (hg : Integrable g (volume : Measure ℝ))
    (a b : ℝ × ℝ → ℝ) (ha : Measurable a) (hb : Measurable b) :
    AEMeasurable (fun p : ℝ × ℝ => ∫ y in Set.Ioc (a p) (b p), g y)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  classical
  set F : (ℝ × ℝ) × ℝ → ℂ := fun q => (Set.Ioc (a q.1) (b q.1)).indicator g q.2 with hFdef
  have hs : MeasurableSet {q : (ℝ × ℝ) × ℝ | a q.1 < q.2 ∧ q.2 ≤ b q.1} := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (ha.comp measurable_fst) measurable_snd
    · exact measurableSet_le measurable_snd (hb.comp measurable_fst)
  have hgm : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => g q.2)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) :=
    hg.aestronglyMeasurable.comp_snd
  have hfind : AEStronglyMeasurable
      ({q : (ℝ × ℝ) × ℝ | a q.1 < q.2 ∧ q.2 ≤ b q.1}.indicator (fun q => g q.2))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) :=
    hgm.indicator hs
  have hFeq : ({q : (ℝ × ℝ) × ℝ | a q.1 < q.2 ∧ q.2 ≤ b q.1}.indicator
      (fun q => g q.2)) = F := by
    funext q
    by_cases h : a q.1 < q.2 ∧ q.2 ≤ b q.1
    · have h1 : q ∈ {q : (ℝ × ℝ) × ℝ | a q.1 < q.2 ∧ q.2 ≤ b q.1} := h
      have h2 : q.2 ∈ Set.Ioc (a q.1) (b q.1) := h
      rw [Set.indicator_of_mem h1, hFdef]
      exact (Set.indicator_of_mem h2 g).symm
    · have h1 : q ∉ {q : (ℝ × ℝ) × ℝ | a q.1 < q.2 ∧ q.2 ≤ b q.1} := h
      have h2 : q.2 ∉ Set.Ioc (a q.1) (b q.1) := h
      rw [Set.indicator_of_notMem h1, hFdef]
      exact (Set.indicator_of_notMem h2 g).symm
  have hF : AEStronglyMeasurable F
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) :=
    hFeq ▸ hfind
  have hInt : AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ y, F (p, y))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    hF.integral_prod_right'
  refine hInt.aemeasurable.congr ?_
  refine Filter.Eventually.of_forall (fun p => ?_)
  have heq : ∫ y, F (p, y) = ∫ y in Set.Ioc (a p) (b p), g y := by
    simp only [hFdef]
    exact MeasureTheory.integral_indicator measurableSet_Ioc
  exact heq

theorem aemeasurable_grid_shift_average_uncurry (k : ℤ) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun p : ℝ × ℝ => ((2:ℝ)^k) •
      ∫ y in Set.Ioc (p.1 + (⌊(p.2 - p.1) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
        (p.1 + (⌊(p.2 - p.1) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have ha : Measurable (fun p : ℝ × ℝ =>
      p.1 + (⌊(p.2 - p.1) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k)) := by measurability
  have hb : Measurable (fun p : ℝ × ℝ =>
      p.1 + (⌊(p.2 - p.1) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)) :=
    ha.add measurable_const
  have hmain := aemeasurable_setIntegral_Ioc_volume g hg
    (fun p : ℝ × ℝ => p.1 + (⌊(p.2 - p.1) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
    (fun p : ℝ × ℝ => p.1 + (⌊(p.2 - p.1) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k))
    ha hb
  exact hmain.const_smul ((2:ℝ)^k)

end Commons.Analysis.Fourier