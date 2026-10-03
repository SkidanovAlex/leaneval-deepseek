import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps

namespace Work.KMTPlan.A6Aux

/-- The dominating kernel series of `Work.KMTAreas.A7.kernComp` is a.e. measurable in the
time variable: it is the `t`-wise sum over `ℤ × ℤ` of the (nonnegative) products
`‖K (p.1 - z.1) (p.2 - z.2)‖ₑ * (‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ)`, and each summand is a.e.
measurable because it is a constant times the product of the a.e. measurable functions
`t ↦ ‖κ t z.1‖ₑ` and `t ↦ ‖κ' t z.2‖ₑ`. -/
theorem aemeasurable_tsum_enorm_kernDom {K : ℤ → ℤ → ℂ} {κ κ' : ℝ → ℤ → ℂ} {ν : MeasureTheory.Measure ℝ}
    (hmκ : ∀ j : ℤ, AEMeasurable (fun t : ℝ => κ t j) ν)
    (hmκ' : ∀ j : ℤ, AEMeasurable (fun t : ℝ => κ' t j) ν) (p : ℤ × ℤ) :
    AEMeasurable (fun t : ℝ =>
      ∑' z : ℤ × ℤ, ‖K (p.1 - z.1) (p.2 - z.2)‖ₑ * (‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ)) ν := by
  refine AEMeasurable.tsum (fun z => ?_)
  exact AEMeasurable.const_mul (((hmκ z.1).enorm).mul ((hmκ' z.2).enorm)) _

end Work.KMTPlan.A6Aux
