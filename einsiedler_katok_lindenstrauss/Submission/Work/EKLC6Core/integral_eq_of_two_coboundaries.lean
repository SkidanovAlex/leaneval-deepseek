import Mathlib
import Submission.Work.EKLC6Core.coboundary_integral

namespace Work.EKLC6Core

/-- **Integral identity from two coboundary equations.**

Given a measure preserving map `φ` of a probability space `μ` and two almost-everywhere
coboundary identities
`gH - gq - gj = A ∘ φ - A` and `gj - gp - gr = B ∘ φ - B`,
the unknown middle term `gj` cancels on adding, leaving
`gH - gq - gp - gr = (A + B) ∘ φ - (A + B)` a.e.
Since `gH - gq - gp - gr` is integrable, the coboundary `(A+B) ∘ φ - (A+B)` has vanishing
integral (`Work.EKLC6Core.coboundary_integral`, which does not require `A + B` to be
integrable), and the asserted identity follows. -/
theorem integral_eq_of_two_coboundaries {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ]
    {φ : X → X} (hφ : MeasureTheory.MeasurePreserving φ μ μ)
    {A B : X → ℝ} (hA : MeasureTheory.AEStronglyMeasurable A μ)
    (hB : MeasureTheory.AEStronglyMeasurable B μ)
    {gH gq gj gp gr : X → ℝ}
    (hae1 : ∀ᵐ x ∂μ, gH x - gq x - gj x = A (φ x) - A x)
    (hae2 : ∀ᵐ x ∂μ, gj x - gp x - gr x = B (φ x) - B x)
    (hH : MeasureTheory.Integrable gH μ) (hq : MeasureTheory.Integrable gq μ)
    (hp : MeasureTheory.Integrable gp μ) (hr : MeasureTheory.Integrable gr μ) :
    ∫ x, gH x ∂μ = ∫ x, gq x ∂μ + ∫ x, gp x ∂μ + ∫ x, gr x ∂μ := by
  -- The sum of the two coboundary equations, with `gj` cancelled.
  have hdec : ∀ᵐ x ∂μ,
      (fun x => gH x - gq x - gp x - gr x) x
        = (fun x => A x + B x) (φ x) - (fun x => A x + B x) x := by
    filter_upwards [hae1, hae2] with x h1 h2
    show gH x - gq x - gp x - gr x = A (φ x) + B (φ x) - (A x + B x)
    linarith
  -- Integrability of the (combined) coboundary.
  have hDint : MeasureTheory.Integrable (fun x => gH x - gq x - gp x - gr x) μ :=
    ((hH.sub hq).sub hp).sub hr
  have hΨ : MeasureTheory.AEStronglyMeasurable (fun x => A x + B x) μ := hA.add hB
  have hzero : ∫ x, gH x - gq x - gp x - gr x ∂μ = 0 :=
    coboundary_integral hφ hΨ hDint hdec
  -- Expand the integral of the combined coboundary.
  have h1 : ∫ x, gH x - gq x ∂μ = ∫ x, gH x ∂μ - ∫ x, gq x ∂μ :=
    MeasureTheory.integral_sub hH hq
  have h2 : ∫ x, gH x - gq x - gp x ∂μ = ∫ x, gH x - gq x ∂μ - ∫ x, gp x ∂μ :=
    MeasureTheory.integral_sub (hH.sub hq) hp
  have h3 : ∫ x, gH x - gq x - gp x - gr x ∂μ
      = ∫ x, gH x - gq x - gp x ∂μ - ∫ x, gr x ∂μ :=
    MeasureTheory.integral_sub ((hH.sub hq).sub hp) hr
  linarith

end Work.EKLC6Core
