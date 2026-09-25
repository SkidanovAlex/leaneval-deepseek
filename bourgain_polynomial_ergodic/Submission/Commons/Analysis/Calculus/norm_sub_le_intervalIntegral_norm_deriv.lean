import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory

namespace Commons.Analysis.Calculus

/-- If `u : ℝ → E` is differentiable on `[a, b]` with derivative `u'`, and `u'` is interval
integrable on `[a, b]`, then `‖u b - u a‖ ≤ ∫ s in a..b, ‖u' s‖`.

No completeness assumption is needed on `E`: the argument first maps everything into the
completion `F` of `E` (a complete normed space), applies the fundamental theorem of calculus
there, and then uses that the canonical embedding `E → F` is a linear isometry. -/
theorem norm_sub_le_intervalIntegral_norm_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u u' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hu : ∀ s ∈ Set.uIcc a b, HasDerivAt u (u' s) s)
    (hint : IntervalIntegrable u' volume a b) :
    ‖u b - u a‖ ≤ ∫ s in a..b, ‖u' s‖ := by
  let F := UniformSpace.Completion E
  let L : E →L[ℝ] F := UniformSpace.Completion.toComplL
  let û : ℝ → F := fun x => L (u x)
  let û' : ℝ → F := fun x => L (u' x)
  -- the canonical embedding into the completion is an isometry
  have hLnorm : ∀ x : E, ‖L x‖ = ‖x‖ := by
    intro x
    change ‖(UniformSpace.Completion.toComplL : E →L[ℝ] F) x‖ = ‖x‖
    simp [UniformSpace.Completion.coe_toComplL]
  -- differentiability transfers to the completion
  have huF : ∀ s ∈ Set.uIcc a b, HasDerivAt û (û' s) s := by
    intro s hs
    have h := (ContinuousLinearMap.hasFDerivAt L).comp_hasDerivAt s (hu s hs)
    simpa only [û, û', Function.comp_def] using h
  -- interval integrability transfers to the completion
  have hintF : IntervalIntegrable û' volume a b := by
    have h1 : IntervalIntegrable (fun s => L (u' s)) volume a b :=
      ⟨L.integrableOn_comp hint.1, L.integrableOn_comp hint.2⟩
    simpa only [û'] using h1
  -- fundamental theorem of calculus in the complete space `F`
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt huF hintF
  have hnorm : ‖û b - û a‖ ≤ ∫ s in a..b, ‖û' s‖ := by
    rw [← key]
    exact intervalIntegral.norm_integral_le_integral_norm hab
  have hnormfun : (fun s => ‖û' s‖) = (fun s => ‖u' s‖) := by
    funext s
    change ‖L (u' s)‖ = ‖u' s‖
    exact hLnorm _
  calc ‖u b - u a‖ = ‖û b - û a‖ := by
        change ‖u b - u a‖ = ‖L (u b) - L (u a)‖
        rw [← map_sub]
        exact (hLnorm _).symm
      _ ≤ ∫ s in a..b, ‖û' s‖ := hnorm
      _ = ∫ s in a..b, ‖u' s‖ := by rw [hnormfun]

end Commons.Analysis.Calculus