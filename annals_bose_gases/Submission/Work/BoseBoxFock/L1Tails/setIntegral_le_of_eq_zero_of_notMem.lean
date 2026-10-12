import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails

theorem setIntegral_le_of_eq_zero_of_notMem {β : Type*} [MeasurableSpace β]
    {μ : MeasureTheory.Measure β} {F : β → ℝ} {s t : Set β}
    (hF : 0 ≤ F) (hsupp : ∀ x, x ∉ t → F x = 0)
    (hint : MeasureTheory.IntegrableOn F t μ) :
    ∫ x in s, F x ∂μ ≤ ∫ x in t, F x ∂μ := by
  -- `F` vanishes off `t`, hence its integral against any measure equals the integral over `t`.
  have h1 : ∫ x, F x ∂(μ.restrict s) = ∫ x in t, F x ∂(μ.restrict s) :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  -- `μ.restrict s` restricted to `t` is dominated by `μ.restrict t`, and `F ≥ 0` is
  -- integrable for the latter by hypothesis.
  have h2 : ∫ x, F x ∂((μ.restrict s).restrict t) ≤ ∫ x, F x ∂(μ.restrict t) :=
    MeasureTheory.integral_mono_measure
      (MeasureTheory.Measure.restrict_mono subset_rfl MeasureTheory.Measure.restrict_le_self)
      (Filter.Eventually.of_forall hF) hint
  calc ∫ x in s, F x ∂μ = ∫ x, F x ∂(μ.restrict s) := rfl
    _ = ∫ x in t, F x ∂(μ.restrict s) := h1
    _ = ∫ x, F x ∂((μ.restrict s).restrict t) := rfl
    _ ≤ ∫ x, F x ∂(μ.restrict t) := h2
    _ = ∫ x in t, F x ∂μ := rfl

end Work.BoseBoxFock.L1Tails
