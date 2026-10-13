import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

theorem integral_le_integral_of_ae_le {s : Set ℝ} {f g : ℝ → ℝ}
    (h : f ≤ᵐ[MeasureTheory.volume.restrict s] g)
    (hg : MeasureTheory.IntegrableOn g s)
    (hg0 : 0 ≤ᵐ[MeasureTheory.volume.restrict s] g) :
    ∫ x in s, f x ≤ ∫ x in s, g x := by
  by_cases hf : MeasureTheory.IntegrableOn f s
  · exact MeasureTheory.integral_mono_ae hf hg h
  · rw [MeasureTheory.integral_undef hf]
    exact MeasureTheory.integral_nonneg_of_ae hg0

end Work.FTS.EllipticEst
