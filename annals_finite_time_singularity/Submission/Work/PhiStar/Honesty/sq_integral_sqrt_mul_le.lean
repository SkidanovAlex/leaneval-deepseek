import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.PhiStar.Honesty

/-- Cauchy–Schwarz for the square roots of two nonnegative integrable functions:
`(∫ √A √B)² ≤ (∫ A)(∫ B)`.  This is the `p = q = 2` Bunyakovsky inequality applied to
`√A` and `√B`, whose squares are `A` and `B` on `s`. -/
theorem sq_integral_sqrt_mul_le {s : Set ℝ} (hs : MeasurableSet s) {A B : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A s) (hB : MeasureTheory.IntegrableOn B s)
    (hAnn : ∀ x ∈ s, 0 ≤ A x) (hBnn : ∀ x ∈ s, 0 ≤ B x) :
    (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x)) ^ 2
      ≤ (∫ x in s, A x) * (∫ x in s, B x) := by
  -- `√A` and `√B` are a.e.-strongly-measurable as continuous images of `A`, `B`.
  have hmeasA : AEStronglyMeasurable (fun x => Real.sqrt (A x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hmeasB : AEStronglyMeasurable (fun x => Real.sqrt (B x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  -- Their squares are `A`, `B` on `s`, hence integrable.
  have hintA : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict s) :=
    hA.congr_fun (fun x hx => (Real.sq_sqrt (hAnn x hx)).symm) hs
  have hintB : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict s) :=
    hB.congr_fun (fun x hx => (Real.sq_sqrt (hBnn x hx)).symm) hs
  have hmemA : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hmeasA).2 hintA
  have hmemB : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hmeasB).2 hintB
  have hcs := Work.Spaces.cs_integral hmemA hmemB
  have hsqA : (∫ x in s, Real.sqrt (A x) ^ 2) = ∫ x in s, A x :=
    setIntegral_congr_fun hs (fun x hx => Real.sq_sqrt (hAnn x hx))
  have hsqB : (∫ x in s, Real.sqrt (B x) ^ 2) = ∫ x in s, B x :=
    setIntegral_congr_fun hs (fun x hx => Real.sq_sqrt (hBnn x hx))
  rw [hsqA, hsqB] at hcs
  exact hcs

end Work.PhiStar.Honesty
