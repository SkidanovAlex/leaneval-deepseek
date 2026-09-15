import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.Analysis.Measure.Fubini

theorem integral_prod_four_left_assoc {α β γ δ E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μa : MeasureTheory.Measure α) (μb : MeasureTheory.Measure β) (μc : MeasureTheory.Measure γ)
    (μd : MeasureTheory.Measure δ)
    [MeasureTheory.SFinite μa] [MeasureTheory.SFinite μb] [MeasureTheory.SFinite μc]
    [MeasureTheory.SFinite μd]
    (F : ((α × β) × γ) × δ → E)
    (hF : MeasureTheory.Integrable F (((μa.prod μb).prod μc).prod μd)) :
    ∫ b, F b ∂(((μa.prod μb).prod μc).prod μd)
      = ∫ a, ∫ b, ∫ c, ∫ d, F (((a, b), c), d) ∂μd ∂μc ∂μb ∂μa := by
  have h1 := MeasureTheory.integral_prod (μ := (μa.prod μb).prod μc) (ν := μd) F hF
  have hG : MeasureTheory.Integrable (fun x : (α × β) × γ => ∫ d, F (x, d) ∂μd)
      ((μa.prod μb).prod μc) :=
    hF.integral_prod_left
  have h2 := MeasureTheory.integral_prod (μ := μa.prod μb) (ν := μc)
      (f := fun x : (α × β) × γ => ∫ d, F (x, d) ∂μd) hG
  have hH : MeasureTheory.Integrable (fun y : α × β => ∫ c, (∫ d, F ((y, c), d) ∂μd) ∂μc)
      (μa.prod μb) :=
    hG.integral_prod_left
  have h3 := MeasureTheory.integral_prod (μ := μa) (ν := μb)
      (f := fun y : α × β => ∫ c, (∫ d, F ((y, c), d) ∂μd) ∂μc) hH
  rw [h1, h2, h3]

end Commons.Analysis.Measure.Fubini