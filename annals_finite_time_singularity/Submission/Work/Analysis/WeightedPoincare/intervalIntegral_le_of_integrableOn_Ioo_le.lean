import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Analysis.WeightedPoincare

theorem intervalIntegral_le_of_integrableOn_Ioo_le {g : ℝ → ℝ} {z J : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1)
    (hnn : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ g t)
    (hg : MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) 1))
    (hJ : ∫ t in Set.Ioo (0 : ℝ) 1, g t ≤ J) :
    ∫ t in (z / 2)..z, g t ≤ J := by
  -- the interval `(z/2, z]` sits inside `(0, 1)` since `0 < z < 1`
  have hz : z / 2 ≤ z := by linarith
  rw [intervalIntegral.integral_of_le hz]
  have hsub : Set.Ioc (z / 2) z ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1, hz0], by linarith [hx.2, hz1]⟩
  have hnn' : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)] g := by
    change ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1), 0 ≤ g x
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall (fun x hx => hnn x hx)
  -- monotonicity of the set integral for a nonnegative integrand
  exact le_trans
    (MeasureTheory.setIntegral_mono_set hg hnn' (Filter.EventuallySubset.of_subset hsub)) hJ

end Work.Analysis.WeightedPoincare
