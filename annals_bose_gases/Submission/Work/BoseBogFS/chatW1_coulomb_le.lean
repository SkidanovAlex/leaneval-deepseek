import ChallengeDeps
import Submission.Work.BoseFixR.W1omegaMassLe
import Submission.Work.BoseFixR.mass_le_W1omega2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open MeasureTheory

theorem chatW1_coulomb_le :
    ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ},
      0 < R → 0 < ℓ → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      R ≤ ℓ * Submission.BoseGases.chiR0 →
      (∫ p : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 2)
        ≤ 512 * Real.pi ^ 4 * (_root_.BoseGases.a v) := by
  intro v h R ℓ hR hℓ hv hvrad hv_supp hRℓ
  have hv01 : 0 ≤ v := hv
  -- integrability of `W₁` from the standing dilute-regime hypotheses
  have hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) := by
    simpa only [Work.BoseFixR.W1fun] using
      Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  -- the sharp momentum mass bound and the `W₁ω` mass bound
  have h1 := Work.BoseFixR.mass_le_W1omega2 (v := v) h hv01 hvrad
      hR hv_supp hRℓ hℓ hW
  have h2 := Work.BoseFixR.W1omegaMassLe (v := v) h hv01 hvrad
      hR hℓ hv_supp hRℓ
  -- `∫ Ŵ₁²/‖p‖² = 2 ∫ Ŵ₁²/(2‖p‖²)`
  have hI2J : (∫ p : EuclideanSpace ℝ (Fin 3),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 2)
      = 2 * ∫ q : EuclideanSpace ℝ (Fin 3),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
    dsimp only
    have hpt : 2 * ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2))
        = (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / ‖q‖ ^ 2 := by
      rcases eq_or_ne (‖q‖) 0 with hb | hb
      · simp [hb]
      · field_simp
    exact hpt.symm
  -- clear the `(2π)⁻³` prefactor
  have hJle : (∫ q : EuclideanSpace ℝ (Fin 3),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2))
      ≤ (2 * Real.pi) ^ 3 * (2 * ∫ x : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1omegaFun v h ℓ x) := by
    have hc : 0 < (2 * Real.pi) ^ 3 := by positivity
    have hh := h1
    rw [inv_mul_le_iff₀ hc] at hh
    exact hh
  -- assembly: `2·(2π)³·2·16π = 512π⁴`
  calc (∫ p : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 2)
      = 2 * ∫ q : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := hI2J
    _ ≤ 2 * ((2 * Real.pi) ^ 3 * (2 * ∫ x : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1omegaFun v h ℓ x)) :=
        mul_le_mul_of_nonneg_left hJle (by norm_num)
    _ ≤ 2 * ((2 * Real.pi) ^ 3 * (2 * (16 * Real.pi * _root_.BoseGases.a v))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [h2]
    _ = 512 * Real.pi ^ 4 * (_root_.BoseGases.a v) := by ring

end Work.BoseBogFS
