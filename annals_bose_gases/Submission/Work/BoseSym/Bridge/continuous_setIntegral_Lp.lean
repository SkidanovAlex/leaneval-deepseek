import Mathlib.MeasureTheory.Function.L2Space
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Bridge

/-- The set integral `f ↦ ∫ x in s, f x ∂μ` is a continuous linear functional on `L²(μ)`
whenever `s` has finite measure: it is the `L²`-pairing against the indicator of `s`. -/
theorem continuous_setIntegral_Lp {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) :
    Continuous (fun f : MeasureTheory.Lp ℝ 2 μ => ∫ x in s, (f : α → ℝ) x ∂μ) := by
  -- Identify the set integral with the inner product against `1_s ∈ L²(μ)`.
  have hg : Continuous fun f : MeasureTheory.Lp ℝ 2 μ =>
      inner ℝ (MeasureTheory.indicatorConstLp 2 hs hμs (1 : ℝ)) f :=
    continuous_inner.comp (continuous_const.prodMk continuous_id)
  refine hg.congr fun f => ?_
  exact MeasureTheory.L2.inner_indicatorConstLp_one hs hμs f

end Work.BoseSym.Bridge
