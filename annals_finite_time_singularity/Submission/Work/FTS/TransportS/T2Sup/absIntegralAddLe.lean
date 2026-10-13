import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.T2Sup

theorem absIntegralAddLe {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} (hf : MeasureTheory.Integrable f μ) :
    |∫ x, (f x + g x) ∂μ| ≤ |∫ x, f x ∂μ| + |∫ x, g x ∂μ| := by
  by_cases hg : MeasureTheory.Integrable g μ
  · rw [MeasureTheory.integral_add hf hg]
    exact abs_add_le _ _
  · have hfg : ¬ MeasureTheory.Integrable (fun x => f x + g x) μ := by
      intro h
      have h2 : ((fun x => f x + g x) - f) = g := by
        funext x
        simp [Pi.sub_apply]
      exact hg (h2 ▸ h.sub hf)
    rw [MeasureTheory.integral_undef hfg, MeasureTheory.integral_undef hg]
    simp

end Work.FTS.TransportS.T2Sup
