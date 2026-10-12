import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.B.pd_aux

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- `boxMean ℓ d u Φ = (boxMass ℓ d u)⁻¹ * ∫ z in dlBox ℓ d u, Φ (fun _ => z)` is a *mean* of
the avatar `z ↦ Φ (fun _ => z)` over the sliding box `dlBox ℓ d u`, so it inherits a pointwise
bound from `Φ`:

    |Φ| ≤ M  ⟹  |boxMean ℓ d u Φ| ≤ M   (for all `u`).

Proof: `boxMass ℓ d u = (volume : Measure ℝ³).real (dlBox ℓ d u) ≥ 0` is the volume of the box.
If it is `0` then `boxMean = 0⁻¹ * _ = 0 ≤ M` (and `M ≥ 0` because `X 1` is nonempty).  Otherwise
`norm_setIntegral_le_of_norm_le_const` bounds the box integral by `M * boxMass ℓ d u`, and
`(boxMass)⁻¹ * (M * boxMass) = M`. -/
theorem boxMean_abs_le {ℓ d M : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X 1 → ℝ} (hΦc : Continuous Φ)
    (hM : ∀ x : Submission.BoseGases.X 1, |Φ x| ≤ M) :
    ∀ u : EuclideanSpace ℝ (Fin 3), |Work.UBBInputs9.B.boxMean ℓ d u Φ| ≤ M := by
  intro u
  -- `X 1` is nonempty, so `0 ≤ M`.
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (Φ (fun _ => (0 : ℝ³)))) (hM _)
  have hfin : (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u) < ⊤ :=
    Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
  -- Bound for the box integral.
  have hJ : |∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (fun _ => z)|
      ≤ M * Work.SmallBoxSliding.boxMass ℓ d u := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := (volume : Measure ℝ³)) (f := fun z : ℝ³ => Φ (fun _ => z))
      (s := Submission.BoseGases.dlBox ℓ d u) (C := M) hfin (fun z _ => hM _)
    rw [Real.norm_eq_abs, ← Work.SmallBoxSliding.boxMass_eq_measureReal] at h
    exact h
  -- `boxMass` is a (nonnegative) volume.
  have hVnn : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal]
    exact ENNReal.toReal_nonneg
  rw [show Work.UBBInputs9.B.boxMean ℓ d u Φ
      = (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
        ∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (fun _ => z) from rfl]
  rcases eq_or_lt_of_le hVnn with hV0 | hVpos
  · -- degenerate box: `boxMean = 0`
    rw [← hV0, inv_zero, zero_mul, abs_zero]
    exact hM0
  · -- genuine mean: divide the integral bound by the box volume
    rw [abs_mul, abs_inv, abs_of_pos hVpos]
    refine le_trans (mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hVnn)) ?_
    have key : (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ * M *
        Work.SmallBoxSliding.boxMass ℓ d u = M := by
      rw [mul_assoc, mul_comm M (Work.SmallBoxSliding.boxMass ℓ d u), ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hVpos), one_mul]
    rw [← mul_assoc, key]

end Work.UBBInputs9.B.pd_aux
