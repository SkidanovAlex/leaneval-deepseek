import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.CutFibreForms
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.cutForm_fsKin_le`

The per-slot `p`-space form of the cutoff symbol `fsKinCoeff c = [r − c]₊²` is dominated by
twice the `(·)²`-form plus `2c²` times the mass form:

    `cutSlotForm χ (fsKinCoeff c) i Ψ ≤ 2·cutSlotForm χ (·)² i Ψ + 2c²·cutSlotForm χ 1 i Ψ`.

**Proof.**  All three forms are `(2π)⁻³ ∫_p F ‖p‖ · cutSlotAmp p`, so the claim is the integral
of the pointwise symbol bound `[r − c]₊² ≤ 2r² + 2c²` (`Work.BSKinetic.Decomp.fsKinCoeff_le_two_mul`)
against the nonnegative amplitude `cutSlotAmp` (nonnegative because `L > 0`), followed by
linearity of the dominating integral.  The two integrability hypotheses on the statement supply
exactly the two Bochner integrals the linearity step needs; this is what rules out the
"junk-value" degeneracy in which the mass form vanishes by convention while the `(·)²`-form does
not (`Submission/Work/UBBInputs9/B/cutoff_loss_note.lean`).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem cutForm_fsKin_le {N : ℕ} {L : ℝ} (hL : 0 < L)
    {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (c : ℝ) (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ}
    (hintD : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 *
      Work.BoseFixB1B.cutSlotAmp L A volA χ i Ψ p))
    (hintM : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1B.cutSlotAmp L A volA χ i Ψ p)) :
    Work.BoseFixB1B.cutSlotForm L A volA χ (Submission.BoseGases.fsKinCoeff c) i Ψ
      ≤ 2 * Work.BoseFixB1B.cutSlotForm L A volA χ (fun t => t ^ 2) i Ψ
        + 2 * c ^ 2 * Work.BoseFixB1B.cutSlotForm L A volA χ (fun _ => 1) i Ψ := by
  classical
  have hpre : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  -- the slot amplitude is pointwise nonnegative (`L > 0`)
  have hamp_nonneg : ∀ p : E3, 0 ≤ cutSlotAmp L A volA χ i Ψ p := by
    intro p
    rw [cutSlotAmp]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hL.le 3))
      (setIntegral_nonneg (Submission.BoseGases.abox_measurable N L)
        (fun x _ => sq_nonneg _))
  -- the dominating integrand is integrable, by the two displayed hypotheses
  have hGint : Integrable (fun p : E3 =>
      (2 * ‖p‖ ^ 2 + 2 * c ^ 2) * cutSlotAmp L A volA χ i Ψ p) := by
    have h1 : Integrable (fun p : E3 =>
        2 * (‖p‖ ^ 2 * cutSlotAmp L A volA χ i Ψ p)) := hintD.const_mul 2
    have h2 : Integrable (fun p : E3 =>
        (2 * c ^ 2) * cutSlotAmp L A volA χ i Ψ p) := hintM.const_mul (2 * c ^ 2)
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply]
    ring
  -- the pointwise symbol bound passes to the integrals
  have hmono : (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ * cutSlotAmp L A volA χ i Ψ p)
      ≤ ∫ p : E3, (2 * ‖p‖ ^ 2 + 2 * c ^ 2) * cutSlotAmp L A volA χ i Ψ p := by
    refine integral_mono_of_nonneg ?_ hGint ?_
    · exact Filter.Eventually.of_forall fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (hamp_nonneg p)
    · exact Filter.Eventually.of_forall fun p =>
        mul_le_mul_of_nonneg_right (Work.BSKinetic.Decomp.fsKinCoeff_le_two_mul c ‖p‖)
          (hamp_nonneg p)
  -- linearity of the dominating integral
  have hsplit : (∫ p : E3, (2 * ‖p‖ ^ 2 + 2 * c ^ 2) * cutSlotAmp L A volA χ i Ψ p)
      = 2 * (∫ p : E3, ‖p‖ ^ 2 * cutSlotAmp L A volA χ i Ψ p)
        + 2 * c ^ 2 * (∫ p : E3, cutSlotAmp L A volA χ i Ψ p) := by
    have hpt : (fun p : E3 => (2 * ‖p‖ ^ 2 + 2 * c ^ 2) * cutSlotAmp L A volA χ i Ψ p)
        = fun p : E3 => 2 * (‖p‖ ^ 2 * cutSlotAmp L A volA χ i Ψ p)
            + (2 * c ^ 2) * cutSlotAmp L A volA χ i Ψ p := by
      funext p
      ring
    rw [hpt, integral_add (hintD.const_mul 2) (hintM.const_mul (2 * c ^ 2)),
      integral_const_mul, integral_const_mul]
  -- the two form identities
  have hform2 : cutSlotForm L A volA χ (fun t => t ^ 2) i Ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 * cutSlotAmp L A volA χ i Ψ p := by
    simp only [cutSlotForm]
  have hform1 : cutSlotForm L A volA χ (fun _ => 1) i Ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, cutSlotAmp L A volA χ i Ψ p := by
    simp only [cutSlotForm, one_mul]
  calc
    cutSlotForm L A volA χ (Submission.BoseGases.fsKinCoeff c) i Ψ
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖
            * cutSlotAmp L A volA χ i Ψ p := rfl
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, (2 * ‖p‖ ^ 2 + 2 * c ^ 2)
            * cutSlotAmp L A volA χ i Ψ p := mul_le_mul_of_nonneg_left hmono hpre
    _ = 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 * cutSlotAmp L A volA χ i Ψ p)
          + 2 * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
              cutSlotAmp L A volA χ i Ψ p) := by
        rw [hsplit]
        ring
    _ = 2 * cutSlotForm L A volA χ (fun t => t ^ 2) i Ψ
          + 2 * c ^ 2 * cutSlotForm L A volA χ (fun _ => 1) i Ψ := by
        rw [hform2, hform1]

end Work.BoseFixB1B
