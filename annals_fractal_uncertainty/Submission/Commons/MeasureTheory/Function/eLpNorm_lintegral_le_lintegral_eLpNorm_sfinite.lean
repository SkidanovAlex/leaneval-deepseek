import Submission.Commons.Analysis.Integral.eLpNorm_integral_le_lintegral_eLpNorm_sfinite

namespace Commons.MeasureTheory.Function

/-- Minkowski's integral inequality (in the `Lᵖ`-seminorm form) for `ℝ≥0∞`-valued kernels,
in the `s`-finite case.  This is the symmetric form of
`Commons.Analysis.Integral.lintegral_lintegral_le_lintegral_lintegral`: the `Lᵖ`-norm of the
fibre integrals is at most the integral of the `Lᵖ`-norms of the fibres. -/
theorem eLpNorm_lintegral_le_lintegral_eLpNorm_sfinite {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] {p : ENNReal} (hp1 : 1 ≤ p)
    (hptop : p ≠ ⊤) {F : α → β → ENNReal} (hF : AEMeasurable (Function.uncurry F) (μ.prod ν)) :
    MeasureTheory.eLpNorm (fun x => ∫⁻ y, F x y ∂ν) p μ
      ≤ ∫⁻ y, MeasureTheory.eLpNorm (fun x => F x y) p μ ∂ν := by
  have hg : AEMeasurable (Function.uncurry (fun y x => F x y)) (ν.prod μ) :=
    AEMeasurable.prod_swap hF
  exact Commons.Analysis.Integral.lintegral_lintegral_le_lintegral_lintegral hp1 hg

end Commons.MeasureTheory.Function
