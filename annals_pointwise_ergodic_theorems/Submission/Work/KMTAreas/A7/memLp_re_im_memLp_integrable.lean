import Mathlib

set_option linter.unusedVariables false

namespace Work.KMTAreas.A7

/-- If a complex-valued function on `ℤ` belongs to `ℓᵖ` for the counting measure, then so do
its real and imaginary parts (they are dominated pointwise by the modulus). -/
theorem memLp_re_im_memLp_integrable {p : ℝ} (hp : 0 < p) {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) :
    MeasureTheory.MemLp (fun x : ℤ => (f x).re) (ENNReal.ofReal p)
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ∧
      MeasureTheory.MemLp (fun x : ℤ => (f x).im) (ENNReal.ofReal p)
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
  ⟨hf.re, hf.im⟩

end Work.KMTAreas.A7
