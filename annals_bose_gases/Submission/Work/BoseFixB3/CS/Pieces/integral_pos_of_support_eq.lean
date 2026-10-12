import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

theorem integral_pos_of_support_eq {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {s : Set α} {f g : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfi : MeasureTheory.IntegrableOn f s μ)
    (hg0 : ∀ x, 0 ≤ g x) (hgi : MeasureTheory.IntegrableOn g s μ)
    (hfg : ∀ x, f x = 0 ↔ g x = 0)
    (h : 0 < ∫ x in s, f x ∂μ) : 0 < ∫ x in s, g x ∂μ := by
  -- The hypothesis `hfg` says the pointwise zero sets of `f` and `g` agree,
  -- hence their supports (as sets) coincide.
  have hsupp : Function.support f = Function.support g := by
    ext x
    simp only [Function.mem_support]
    exact not_congr (hfg x)
  -- Both are nonnegative, so the positivity of the set integral is equivalent
  -- to the measure of `support ∩ s` being positive.
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgi,
    ← hsupp]
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfi] at h
  exact h

end Work.BoseFixB3.CS.Pieces
