import ChallengeDeps
import Submission.Work.BoseBogFS.continuous_chat
import Submission.Work.BoseFixR.IntegrableChatW1sq
import Submission.Work.BoseRowsL.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped ENNReal

set_option linter.unusedVariables false

namespace Work.BoseRowsL.Tails

/-- **The Coulomb double `∫⁻` in position space controls the diagonal momentum integrand.**

For an `L¹` kernel `W` on `ℝ³` whose position-space Coulomb energy
`∫⁻ x, ∫⁻ y, ofReal (W x · W y / ‖x − y‖)` is finite, the kinetic-energy density
`Ŵ(k)²/(2‖k‖²)` (`Ŵ = Work.BoseFixR.chat W`) is integrable.

Route (existing corpus lemmas, no new imports):
* `Work.BoseFixR.lintegral_chat_le_kinFT` — `(Ŵ(k))² ≤ ‖kinFT W k‖²` under the `∫⁻`;
* `Work.BoseFixR.fourier_coulomb_le` — the momentum Coulomb inequality
  `ofReal((2π)³⁻¹)·∫⁻‖kinFT W‖²/‖k‖² ≤ ofReal(1/(4π))·(position-space double `∫⁻`)`;
  multiplying by the finite constant `ofReal((2π)³) = (ofReal((2π)³⁻¹))⁻¹` and combining
  bounds the momentum `∫⁻` by a finite constant times the (finite) double `∫⁻`.
Then `MeasureTheory.hasFiniteIntegral_iff_ofReal` plus continuity of `chat`
(`Work.BoseFixR.continuous_chat`) give `MeasureTheory.Integrable`. -/
lemma chat_sq_div_integrable_of_coulomb_finite {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hWnn : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ W x)
    (hfin : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2)) := by
  have hstep1 := Work.BoseFixR.lintegral_chat_le_kinFT W
  have hfour := Work.BoseFixR.fourier_coulomb_le W hW hWnn
  -- `ofReal((2π)³) · ofReal((2π)³⁻¹) = 1`
  have hc : ENNReal.ofReal ((2 * Real.pi) ^ 3) * ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi) ^ 3),
      mul_inv_cancel₀ (by positivity : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0), ENNReal.ofReal_one]
  -- un-normalise the momentum `∫⁻`
  have hXle : (∫⁻ q : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (‖Submission.BoseGases.kinFT
          (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2))
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3) *
        (ENNReal.ofReal (1 / (4 * Real.pi)) *
          (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
            ENNReal.ofReal (W x * W y / ‖x - y‖))) := by
    calc (∫⁻ q : EuclideanSpace ℝ (Fin 3),
            ENNReal.ofReal (‖Submission.BoseGases.kinFT
              (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2))
        = (ENNReal.ofReal ((2 * Real.pi) ^ 3) * ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)) *
            (∫⁻ q : EuclideanSpace ℝ (Fin 3),
              ENNReal.ofReal (‖Submission.BoseGases.kinFT
                (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2)) := by
          rw [hc, one_mul]
      _ = ENNReal.ofReal ((2 * Real.pi) ^ 3) *
            (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) *
              (∫⁻ q : EuclideanSpace ℝ (Fin 3),
                ENNReal.ofReal (‖Submission.BoseGases.kinFT
                  (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2))) := by
          rw [mul_assoc]
      _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3) *
            (ENNReal.ofReal (1 / (4 * Real.pi)) *
              (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
                ENNReal.ofReal (W x * W y / ‖x - y‖))) :=
          mul_le_mul_of_nonneg_left hfour zero_le
  have hne : (∫⁻ q : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal
      ((Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2))) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)))
      (le_trans hstep1 (mul_le_mul_of_nonneg_left hXle zero_le))
  refine ⟨?_, ?_⟩
  · have hm : Measurable (fun q : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2)) :=
      ((Work.BoseFixR.continuous_chat W hW).measurable.pow_const 2).div
        (measurable_const.mul (continuous_norm.measurable.pow_const 2))
    exact hm.aestronglyMeasurable
  · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun q => by positivity))]
    exact lt_top_iff_ne_top.mpr hne

theorem integrable_chat_g0_sq {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q) ^ 2 / (2 * ‖q‖ ^ 2)) := by
  -- `g₀` is `L¹`, a.e. nonnegative, and its position-space Coulomb energy is finite.
  have hv : (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ≤ v := hv_nonneg
  have hℓ : 0 < R / Submission.BoseGases.chiR0 := div_pos hR Submission.BoseGases.chiR0_pos
  have hRℓ : R ≤ (R / Submission.BoseGases.chiR0) * Submission.BoseGases.chiR0 := by
    rw [div_mul_cancel₀ _ (ne_of_gt Submission.BoseGases.chiR0_pos)]
  have hfin : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (Submission.BoseGases.g0 v h x * Submission.BoseGases.g0 v h y
        / ‖x - y‖)) ≠ ⊤ :=
    (Work.BoseRowsFS.W1_g0_finite (v := v) (R := R)
      (ℓ := R / Submission.BoseGases.chiR0) hR hℓ hv_nonneg hvrad hv_supp h hRℓ).2.1
  exact chat_sq_div_integrable_of_coulomb_finite
    (Submission.BoseGases.g0_integrable hR hv_supp h)
    (Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h) hfin

end Work.BoseRowsL.Tails
