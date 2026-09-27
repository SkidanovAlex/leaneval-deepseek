import Mathlib

namespace Work.EKLComp

/-- Integral over `s` of `s.indicator (g - c)`: since the indicator is `g - c` on `s`, this is
`∫_s g - c * μ(s)`.  The hypothesis `hμs : μ s ≠ ⊤` is needed: without it the constant `c` need
not be integrable on `s` (e.g. `s = univ`, `μ = volume`, `c = 1`), and the identity fails.
(Used with `s` the invariant "bad set" and `c = ε`, in a probability measure.) -/
theorem setIntegral_indicator_sub_const {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (g : X → ℝ)
    (hg : MeasureTheory.Integrable g μ) (c : ℝ) :
    ∫ x in s, s.indicator (fun y => g y - c) x ∂μ = ∫ x in s, g x ∂μ - c * (μ s).toReal := by
  -- On `s` the indicator of `g - c` agrees with `g - c`, so the set integral is that of `g - c`.
  have hcongr : ∫ x in s, s.indicator (fun y => g y - c) x ∂μ = ∫ x in s, (g x - c) ∂μ :=
    MeasureTheory.setIntegral_congr_fun hs (fun x hx => Set.indicator_of_mem hx _)
  -- Split the integral of the difference; the constant is integrable on `s` since `μ s ≠ ⊤`.
  have h2 : ∫ x in s, (g x - c) ∂μ = ∫ x in s, g x ∂μ - ∫ x in s, c ∂μ :=
    MeasureTheory.integral_sub hg.integrableOn (MeasureTheory.integrableOn_const hμs)
  rw [hcongr, h2, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def]
  ring

end Work.EKLComp
