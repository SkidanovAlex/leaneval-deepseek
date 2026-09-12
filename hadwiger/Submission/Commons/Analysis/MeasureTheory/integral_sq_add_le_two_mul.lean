import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open scoped ENNReal
open MeasureTheory

namespace Commons.Analysis.MeasureTheory

theorem integral_sq_add_le_two_mul {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {a b : α → ℝ}
    (ha : MeasureTheory.MemLp a 2 μ) (hb : MeasureTheory.MemLp b 2 μ) :
    (∫ x : α, (a x + b x)^2 ∂μ) ≤
      2 * (∫ x : α, (a x)^2 ∂μ) + 2 * (∫ x : α, (b x)^2 ∂μ) := by
  -- pointwise inequality (a x + b x)^2 ≤ 2 (a x)^2 + 2 (b x)^2
  have hpoint : ∀ x : α, (a x + b x)^2 ≤ 2 * (a x)^2 + 2 * (b x)^2 := by
    intro x
    nlinarith [sq_nonneg (a x - b x)]
  -- integrability of the squares
  have hiA : Integrable (fun x : α => (a x)^2) μ := ha.integrable_sq
  have hiB : Integrable (fun x : α => (b x)^2) μ := hb.integrable_sq
  have hab : MemLp (fun x : α => a x + b x) 2 μ := ha.add hb
  have hiAB : Integrable (fun x : α => (a x + b x)^2) μ := hab.integrable_sq
  have h2A : Integrable (fun x : α => 2 * (a x)^2) μ := hiA.const_mul 2
  have h2B : Integrable (fun x : α => 2 * (b x)^2) μ := hiB.const_mul 2
  calc
    (∫ x : α, (a x + b x)^2 ∂μ)
        ≤ ∫ x : α, (2 * (a x)^2 + 2 * (b x)^2) ∂μ := by
          refine integral_mono hiAB (h2A.add h2B) ?_
          intro x
          exact hpoint x
    _ = 2 * (∫ x : α, (a x)^2 ∂μ) + 2 * (∫ x : α, (b x)^2 ∂μ) := by
          rw [integral_add h2A h2B, integral_const_mul, integral_const_mul]

end Commons.Analysis.MeasureTheory