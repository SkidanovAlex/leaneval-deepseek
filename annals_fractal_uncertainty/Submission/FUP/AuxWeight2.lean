import Submission.FUP.AuxWeight
import Submission.FUP.ExtensionOperator
import Submission.FUP.ModifyWeightFinal
import Submission.FUP.EomegaHessian
import Submission.Commons.Analysis.Calculus.omega0_iteratedFDeriv_le
import Submission.Commons.Analysis.Calculus.Gstar_omega0_le
import Submission.Commons.Measure.Real.integrableOn_log_rpow_decay
import Submission.Commons.Measure.Real.integrableOn_one_add_sq_inv_Ioi

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# The auxiliary plurisubharmonic weight `u₀` of §5

Cohen's §5 uses the plurisubharmonic extension of

  `ω₀(x) = -χ(‖x‖)·‖x‖ / (log(2+‖x‖))²`

(`AuxWeight.lean`), rescaled so that it is `1`-Lipschitz on `ℝᵈ` with `|y|`-growth at most `1/2`.
The scaling constant depends only on `d`, so `u₀` is a *fixed* function.

This module proves

* `contDiff_omega0` (`ω₀ ∈ C³`, needed for `BM_step1_statement`);
* `hasFiniteGrowth_omega0` (the Beurling–Malliavin growth functional of `ω₀` is finite);
* `exists_u0`: the existence of `u₀` with all the properties used in §5.
-/

namespace Submission.FUP

theorem contDiff_omega0 : ContDiff ℝ 3 (omega0 (d := d)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝᵈ) (by norm_num : (0:ℝ) < 5)] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact omega0_eq_zero_of_norm_le_5 hy.le
  · have hn : ContDiffAt ℝ 3 (fun y : ℝᵈ => ‖y‖) x := contDiffAt_norm (𝕜 := ℝ) hx
    have h1 : ContDiffAt ℝ 3 (fun y : ℝᵈ => Real.smoothTransition (‖y‖ / 5 - 1)) x := by
      have hsc : ContDiffAt ℝ 3 Real.smoothTransition (‖x‖ / 5 - 1) :=
        Real.smoothTransition.contDiffAt
      exact hsc.comp x ((hn.div_const 5).sub contDiffAt_const)
    have h2 : ContDiffAt ℝ 3 (fun y : ℝᵈ => ‖y‖ / (Real.log (2 + ‖y‖)) ^ 2) x := by
      have hlog' : ContDiffAt ℝ 3 (fun y : ℝᵈ => Real.log (‖y‖ + 2)) x :=
        (hn.add (contDiffAt_const (c := (2:ℝ)))).log
          (ne_of_gt (by linarith [norm_nonneg x] : (0:ℝ) < ‖x‖ + 2))
      have hlog : ContDiffAt ℝ 3 (fun y : ℝᵈ => Real.log (2 + ‖y‖)) x := by
        simpa [add_comm] using hlog'
      exact hn.div (hlog.pow 2)
        (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [norm_nonneg x]))))
    exact (h1.mul h2).neg

/-- **The Beurling–Malliavin growth condition for `ω₀`.** -/
theorem hasFiniteGrowth_omega0 (hd : 1 ≤ d) :
    ∃ Cgr : ℝ, 0 < Cgr ∧ HasFiniteGrowth (omega0 (d := d)) Cgr := by
  obtain ⟨K, hKpos, hKle⟩ := Commons.Analysis.Calculus.Gstar_omega0_le (d := d)
  have hKnn : 0 ≤ K := hKpos.le
  have hlog_int : IntegrableOn
      (fun r : ℝ => K * (r / (Real.log (2 + r)) ^ 2 / (1 + r ^ 2))) (Set.Ioi (0:ℝ)) := by
    have h := (Commons.Measure.Real.integrableOn_log_rpow_decay 2 (by norm_num)).const_mul K
    refine h.congr ?_
    filter_upwards with r
    simp only [Real.rpow_two]
  have hMajint : IntegrableOn
      (fun r : ℝ => K * (1 + r ^ 2)⁻¹ + K * (r / (Real.log (2 + r)) ^ 2 / (1 + r ^ 2)))
      (Set.Ioi (0:ℝ)) :=
    ((Commons.Measure.Real.integrableOn_one_add_sq_inv_Ioi).const_mul K).add hlog_int
  have hMajnn : ∀ r ∈ Set.Ioi (0:ℝ),
      (0:ℝ) ≤ K * (1 + r ^ 2)⁻¹ + K * (r / (Real.log (2 + r)) ^ 2 / (1 + r ^ 2)) := by
    intro r hr
    have hr0 : 0 < r := hr
    exact add_nonneg (mul_nonneg hKnn (inv_nonneg.mpr (by positivity)))
      (mul_nonneg hKnn (div_nonneg (div_nonneg hr0.le (sq_nonneg _)) (by positivity)))
  have hpt : ∀ r ∈ Set.Ioi (0:ℝ),
      Gstar (omega0 (d := d)) r / (1 + r ^ 2)
        ≤ K * (1 + r ^ 2)⁻¹ + K * (r / (Real.log (2 + r)) ^ 2 / (1 + r ^ 2)) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hlr : (0:ℝ) < Real.log (2 + r) := Real.log_pos (by linarith)
    have h1 : Gstar (omega0 (d := d)) r ≤ K * (1 + r / (Real.log (2 + r)) ^ 2) := hKle r hr0
    have hden : 0 < 1 + r ^ 2 := by positivity
    have h2 : Gstar (omega0 (d := d)) r / (1 + r ^ 2)
        ≤ K * (1 + r / (Real.log (2 + r)) ^ 2) / (1 + r ^ 2) :=
      div_le_div_of_nonneg_right h1 hden.le
    have heq : K * (1 + r / (Real.log (2 + r)) ^ 2) / (1 + r ^ 2)
        = K * (1 + r ^ 2)⁻¹ + K * (r / (Real.log (2 + r)) ^ 2 / (1 + r ^ 2)) := by
      field_simp
    rw [← heq]
    exact h2
  have hint : IntegrableOn (fun r : ℝ => Gstar (omega0 (d := d)) r / (1 + r ^ 2))
      (Set.Ioi (0:ℝ)) := by
    refine Integrable.mono hMajint ?_ ?_
    · refine AEMeasurable.aestronglyMeasurable ?_
      refine AEMeasurable.div ?_ ?_
      · exact (aestronglyMeasurable_Gstar (d := d) hd contDiff_omega0.continuous).aemeasurable
      · exact (continuous_const.add (continuous_id.pow 2)).aemeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Gstar_nonneg _ _) (by positivity : (0:ℝ) ≤ 1 + r ^ 2)),
        abs_of_nonneg (hMajnn r hr)]
      exact hpt r hr
  refine ⟨(∫ r in Set.Ioi (0:ℝ), (K * (1 + r ^ 2)⁻¹
      + K * (r / (Real.log (2 + r)) ^ 2 / (1 + r ^ 2)))) + 1, ?_, hint, ?_⟩
  · have hnn : (0:ℝ) ≤ ∫ r in Set.Ioi (0:ℝ), (K * (1 + r ^ 2)⁻¹
        + K * (r / (Real.log (2 + r)) ^ 2 / (1 + r ^ 2))) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hMajnn r hr
    linarith
  · have hmono : (∫ r in Set.Ioi (0:ℝ), Gstar (omega0 (d := d)) r / (1 + r ^ 2))
        ≤ ∫ r in Set.Ioi (0:ℝ), (K * (1 + r ^ 2)⁻¹
          + K * (r / (Real.log (2 + r)) ^ 2 / (1 + r ^ 2))) :=
      integral_mono_ae hint hMajint (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact hpt r hr)
    simp only [growthFunctional]
    linarith

/-- **The auxiliary weight `u₀` of §5**: plurisubharmonic, `≤ 0` on `ℝᵈ`, `0` on `B₂`,
`1`-Lipschitz on `ℝᵈ`, and with `|Im|`-growth at most `1/2`.  Its construction depends only on
`d`, so `u₀` is a fixed function of `d`. -/
theorem exists_u0 (hd : 1 ≤ d) :
    ∃ u0 : ℂᵈ → ℝ, IsPSH u0 ∧
      (∀ x : ℝᵈ, u0 (toCpx x) ≤ 0) ∧
      (∃ lam : ℝ, 0 < lam ∧ ∀ x : ℝᵈ, u0 (toCpx x) ≤ lam * omega0 x) ∧
      (∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0) ∧
      (∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖) ∧
      (∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
        u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖) := by
  obtain ⟨Creg, hCreg, hreg⟩ := Commons.Analysis.Calculus.omega0_iteratedFDeriv_le (d := d)
  obtain ⟨Cgr, hCgr, hgrowth⟩ := hasFiniteGrowth_omega0 (d := d) hd
  obtain ⟨CLip, ρ, hCLip, hρ, hstep⟩ :=
    BM_step1_of_components (d := d) (modify_weight_statement_proof hd)
      (exact_psh_extension_statement_proof d) Creg Cgr hCreg hCgr
  have hreg' : ∀ (a : ℕ), a ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ a (omega0 (d := d)) x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) := by
    intro a ha x
    have hfun : omega0 (d := d) = fun x : ℝᵈ =>
        -(Real.smoothTransition (‖x‖ / 5 - 1) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2)) := rfl
    have h := hreg a ha x
    simpa only [hfun] using h
  have hzero' : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → omega0 (d := d) x = 0 :=
    fun x hx => omega0_eq_zero_of_norm_le_two (d := d) hx
  obtain ⟨u, hupsh, hule, huzero, hulip, hugrowth⟩ :=
    hstep (omega0 (d := d)) (fun x => omega0_nonpos (d := d) x) hzero' contDiff_omega0
      hreg' hgrowth
  set lam : ℝ := min (1 / CLip) (1 / (2 * ρ)) with hlam
  have hlam_pos : 0 < lam := by
    rw [hlam]; exact lt_min (by positivity) (by positivity)
  have hlam_Clip : lam * CLip ≤ 1 := by
    have h : lam ≤ 1 / CLip := by rw [hlam]; exact min_le_left _ _
    calc lam * CLip ≤ (1 / CLip) * CLip := mul_le_mul_of_nonneg_right h hCLip.le
      _ = 1 := by field_simp
  have hlam_rho : lam * ρ ≤ 1 / 2 := by
    have h : lam ≤ 1 / (2 * ρ) := by rw [hlam]; exact min_le_right _ _
    calc lam * ρ ≤ (1 / (2 * ρ)) * ρ := mul_le_mul_of_nonneg_right h hρ.le
      _ = 1 / 2 := by field_simp
  refine ⟨fun z => lam * u z, hupsh.const_mul hlam_pos.le, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact mul_nonpos_of_nonneg_of_nonpos hlam_pos.le
      (le_trans (hule x) (omega0_nonpos x))
  · exact ⟨lam, hlam_pos, fun x => mul_le_mul_of_nonneg_left (hule x) hlam_pos.le⟩
  · intro x hx
    show lam * u (toCpx x) = 0
    rw [huzero x hx, mul_zero]
  · intro x₁ x₂
    have h1 : lam * u (toCpx x₁) - lam * u (toCpx x₂)
        = lam * (u (toCpx x₁) - u (toCpx x₂)) := by ring
    rw [h1, abs_mul, abs_of_pos hlam_pos]
    calc lam * |u (toCpx x₁) - u (toCpx x₂)|
        ≤ lam * (CLip * ‖x₁ - x₂‖) := mul_le_mul_of_nonneg_left (hulip x₁ x₂) hlam_pos.le
      _ = (lam * CLip) * ‖x₁ - x₂‖ := by ring
      _ ≤ 1 * ‖x₁ - x₂‖ := mul_le_mul_of_nonneg_right hlam_Clip (norm_nonneg _)
  · intro z
    obtain ⟨h1, h2⟩ := hugrowth z
    constructor
    · exact mul_le_mul_of_nonneg_left h1 hlam_pos.le
    · calc lam * u z ≤ lam * (u (toCpx (reVec z)) + ρ * ‖imVec z‖) :=
          mul_le_mul_of_nonneg_left h2 hlam_pos.le
        _ = lam * u (toCpx (reVec z)) + (lam * ρ) * ‖imVec z‖ := by ring
        _ ≤ lam * u (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖ := by
            have := mul_le_mul_of_nonneg_right hlam_rho (norm_nonneg (imVec z))
            linarith

end Submission.FUP
