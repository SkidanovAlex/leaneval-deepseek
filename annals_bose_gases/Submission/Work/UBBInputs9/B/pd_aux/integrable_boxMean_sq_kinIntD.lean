import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `boxMean² · kinIntD`

Given that `boxMean ℓ d · Φ` is a.e. measurable and bounded by `M` on `ℝ³`, and that
`kinIntD ℓ d` is integrable for the product measure `pdMu ℓ`, the product
`(boxMean ℓ d · Φ)² · kinIntD ℓ d` is integrable for `pdMu ℓ`.

The `boxMean²` factor depends only on the first coordinate `u`; `pdMu ℓ` is the product of
Lebesgue measure on `ℝ³` with a restricted measure on `X 1`, so it descends to an a.e.
strongly measurable, bounded function on the product.  The result follows from
`Integrable.bdd_mul` (integrable times bounded a.e.-measurable function is integrable).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B.pd_aux

theorem integrable_boxMean_sq_kinIntD {ℓ d M : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X 1 → ℝ}
    (hEm : AEMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.UBBInputs9.B.boxMean ℓ d u Φ)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), |Work.UBBInputs9.B.boxMean ℓ d u Φ| ≤ M)
    (hId : MeasureTheory.Integrable
      (fun p : (EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X 1 =>
        Work.UBBInputs9.B.kinIntD ℓ d p.1 p.2)
      (Work.UBBInputs9.B.pdMu ℓ)) :
    MeasureTheory.Integrable
      (fun p : (EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X 1 =>
        (Work.UBBInputs9.B.boxMean ℓ d p.1 Φ) ^ 2 * Work.UBBInputs9.B.kinIntD ℓ d p.1 p.2)
      (Work.UBBInputs9.B.pdMu ℓ) := by
  have _ : 0 < ℓ := hℓ
  have _ : 0 < d := hd
  -- `boxMean²` is a.e. strongly measurable on the product, since it is the square of an
  -- a.e. measurable function of the first coordinate.
  have hmeas : AEMeasurable
      (fun p : (EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X 1 =>
        (Work.UBBInputs9.B.boxMean ℓ d p.1 Φ) ^ 2) (Work.UBBInputs9.B.pdMu ℓ) :=
    AEMeasurable.comp_fst (hEm.pow_const 2)
  -- bounds
  have hbound : ∀ᵐ p ∂(Work.UBBInputs9.B.pdMu ℓ),
      ‖(Work.UBBInputs9.B.boxMean ℓ d p.1 Φ) ^ 2‖ ≤ M ^ 2 := by
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Work.UBBInputs9.B.boxMean ℓ d p.1 Φ) ^ 2
        = |Work.UBBInputs9.B.boxMean ℓ d p.1 Φ| ^ 2 := (sq_abs _).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM p.1) 2
  exact MeasureTheory.Integrable.bdd_mul (c := M ^ 2) hId hmeas.aestronglyMeasurable hbound

end Work.UBBInputs9.B.pd_aux
