import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Weil

theorem integrableOn_prod_mul {f g : ℝ → ℝ} {s t : Set ℝ}
    (hf : MeasureTheory.IntegrableOn f s) (hg : MeasureTheory.IntegrableOn g t) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => f p.1 * g p.2) (s ×ˢ t) := by
  rw [MeasureTheory.IntegrableOn] at hf hg ⊢
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    ← MeasureTheory.Measure.prod_restrict s t]
  exact hf.mul_prod hg

end Work.FTS.PhiStar.Series.Weil
