import Mathlib
import Submission.Commons.Analysis.Convex.convexOn_logLaplace
import Submission.Commons.Analysis.Convex.contDiff_logLaplace_penalty
import Submission.Commons.Analysis.Convex.fderiv_le_sub
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm

namespace Commons.Analysis.Asymptotics

open MeasureTheory

/-- **Polynomial growth of the gradient of the log-Laplace penalty.**

For a convex measurable set `A ⊆ ℝ^n` of positive measure and `ε > 0`, the gradient of
`φ x = -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))` grows at most polynomially:
there are `C ≥ 0` and `N` with `‖(fderiv ℝ φ x) v‖ ≤ C * (1 + ‖x‖) ^ N * ‖v‖` for all `x, v`.

This is what is needed to feed the growth hypothesis of the Brascamp–Lieb induction
(`Commons.Analysis.GaussianMeasure.BLon`) for the penalised potential `π‖x‖² + φ_ε`.

Suggested route (avoiding any explicit formula for `∇φ`):
* `φ` is convex — `Commons.Analysis.Convex.convexOn_logLaplace` (available in the commons);
* `φ` is bounded below by the constant `-Real.log (∫ y, Real.exp (-‖y‖ ^ 2 / ε ^ 2))`;
* `φ` is bounded above by a quadratic polynomial: for `R` large enough that
  `volume (A ∩ Metric.ball 0 R) > 0` (possible since `0 < volume A`),
  `∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) ≥ Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2) * volume (A ∩ Metric.ball 0 R)`,
  hence `φ x ≤ (‖x‖ + R) ^ 2 / ε ^ 2 - Real.log (volume (A ∩ Metric.ball 0 R))`;
* for a convex differentiable `φ`, `⟪∇φ x, v⟫ ≤ φ (x + v) - φ x ≤ φ (x + v) - c₀`, so taking
  `v` of norm `1` in the direction of `∇φ x` bounds `‖∇φ x‖` by the polynomial upper bound.
(Alternatively compute `∇(∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))` directly by differentiating
under the integral sign and bound the resulting quotient.) -/
theorem growth_fderiv_logLaplace (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hAm : MeasurableSet A) (hA : Convex ℝ A)
    (hApos : 0 < volume A)
    (hpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n),
      |fderiv ℝ (fun x => -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))) x v|
        ≤ C * (1 + ‖x‖) ^ N * ‖v‖ := by
  classical
  set φ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) with hφ
  -- Convexity and differentiability of `φ`.
  have hconv : ConvexOn ℝ Set.univ φ := by
    rw [hφ]; exact Commons.Analysis.Convex.convexOn_logLaplace n hε A hAm hA
  have hcd : ContDiff ℝ ⊤ φ := by
    rw [hφ]; exact Commons.Analysis.Convex.contDiff_logLaplace_penalty n hε A hAm hpos
  have hdiff : ∀ x, DifferentiableAt ℝ φ x :=
    fun x => (hcd.differentiable (by simp)).differentiableAt
  -- The subgradient inequality for the convex function `φ`.
  have hsub : ∀ x v, fderiv ℝ φ x v ≤ φ (x + v) - φ x :=
    fun x v => Commons.Analysis.Convex.fderiv_le_sub hconv x (hdiff x) v
  -- A uniform lower bound `φ x ≥ -log I`.
  set I : ℝ := ∫ z : EuclideanSpace ℝ (Fin n), Real.exp (-‖z‖ ^ 2 / ε ^ 2) with hI
  have hlower : ∀ x, -Real.log I ≤ φ x := by
    intro x
    have htrans : (∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) = I := by
      rw [hI]
      rw [← integral_sub_right_eq_self (μ := volume)
        (f := fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-‖z‖ ^ 2 / ε ^ 2)) x]
      apply integral_congr_ae
      filter_upwards with y
      rw [norm_sub_rev]
    have hle : (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) ≤ I := by
      rw [← htrans]
      exact setIntegral_le_integral (Commons.Analysis.Convex.integrable_gaussian_translate hε x)
        (ae_of_all _ (fun y => Real.exp_nonneg _))
    have hlog : Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) ≤ Real.log I :=
      Real.log_le_log (hpos x) hle
    simp only [hφ]
    linarith
  -- Existence of a ball of positive measure around `0`.
  obtain ⟨R, hRnn, hRpos⟩ : ∃ R : ℝ, 0 ≤ R ∧ 0 < volume (A ∩ Metric.ball 0 R) := by
    have hcover : (⋃ k : ℕ, A ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ)) = A := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨k, hy, _⟩; exact hy
      · intro hy
        obtain ⟨k, hk⟩ := exists_nat_gt ‖y‖
        exact ⟨k, hy, by rw [Metric.mem_ball, dist_zero_right]; exact hk⟩
    have hne : volume (⋃ k : ℕ, A ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ)) ≠ 0 := by
      rw [hcover]; exact ne_of_gt hApos
    obtain ⟨k, hk⟩ := MeasureTheory.exists_measure_pos_of_not_measure_iUnion_null hne
    exact ⟨(k : ℝ), Nat.cast_nonneg k, hk⟩
  set V : ℝ := (volume (A ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal with hV
  have hVpos : 0 < V := by
    rw [hV, ENNReal.toReal_pos_iff]
    refine ⟨hRpos, ?_⟩
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_ball_lt_top
  have hVne : V ≠ 0 := ne_of_gt hVpos
  -- A quadratic upper bound for `φ`.
  have hupper : ∀ x, φ x ≤ (‖x‖ + R) ^ 2 / ε ^ 2 - Real.log V := by
    intro x
    have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
    set s : Set (EuclideanSpace ℝ (Fin n)) := A ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R with hs
    have hsm : MeasurableSet s := by
      rw [hs]; exact hAm.inter Metric.isOpen_ball.measurableSet
    have hfin : volume s ≠ ⊤ := by
      rw [hs]
      exact (lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_ball_lt_top).ne
    have hpt : ∀ y ∈ s, Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2) ≤ Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) := by
      intro y hy
      apply Real.exp_le_exp.mpr
      have hyR : ‖y‖ < R := by
        have := hy.2
        rwa [Metric.mem_ball, dist_zero_right] at this
      have hxy : ‖x - y‖ ≤ ‖x‖ + R := by
        calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ ‖x‖ + R := by linarith
      have hsq : ‖x - y‖ ^ 2 ≤ (‖x‖ + R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
      rw [neg_div, neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_right hsq hε2.le)
    have hconst_le : (∫ y in s, Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2))
        ≤ ∫ y in s, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) := by
      apply setIntegral_mono_ae_restrict
      · exact integrableOn_const (C := Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2)) hfin (by simp)
      · exact (Commons.Analysis.Convex.integrable_gaussian_translate hε x).integrableOn
      · filter_upwards [MeasureTheory.self_mem_ae_restrict hsm] with y hy
        exact hpt y hy
    have hval : (∫ y in s, Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2))
        = Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2) * V := by
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, ← hV]
      ring
    have hle1 : Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2) * V
        ≤ ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) := by
      rw [← hval]
      calc (∫ y in s, Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2))
          ≤ ∫ y in s, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) := hconst_le
        _ ≤ ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) := by
            apply setIntegral_mono_set
            · exact (Commons.Analysis.Convex.integrable_gaussian_translate hε x).integrableOn
            · exact ae_of_all _ (fun y => Real.exp_nonneg _)
            · rw [hs]; exact ae_of_all _ (fun y hy => hy.1)
    have hlog : Real.log (Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2) * V)
        ≤ Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) :=
      Real.log_le_log (mul_pos (Real.exp_pos _) hVpos) hle1
    have hval2 : -Real.log (Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2) * V)
        = (‖x‖ + R) ^ 2 / ε ^ 2 - Real.log V := by
      rw [Real.log_mul (Real.exp_ne_zero _) hVne, Real.log_exp]
      ring
    simp only [hφ]
    calc -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
        ≤ -Real.log (Real.exp (-(‖x‖ + R) ^ 2 / ε ^ 2) * V) := neg_le_neg hlog
      _ = (‖x‖ + R) ^ 2 / ε ^ 2 - Real.log V := hval2
  -- The bound `B` on the directional derivative in unit directions.
  set K : ℝ := Real.log I - Real.log V with hK
  set B : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => (‖x‖ + 1 + R) ^ 2 / ε ^ 2 + K with hB
  have hunit : ∀ x u, ‖u‖ = 1 → |fderiv ℝ φ x u| ≤ B x := by
    intro x u hu
    have hxu : ‖x + u‖ ≤ ‖x‖ + 1 := by
      calc ‖x + u‖ ≤ ‖x‖ + ‖u‖ := norm_add_le _ _
        _ = ‖x‖ + 1 := by rw [hu]
    have hxmu : ‖x - u‖ ≤ ‖x‖ + 1 := by
      calc ‖x - u‖ ≤ ‖x‖ + ‖u‖ := norm_sub_le _ _
        _ = ‖x‖ + 1 := by rw [hu]
    have hnn1 : (0:ℝ) ≤ ‖x + u‖ + R := add_nonneg (norm_nonneg _) hRnn
    have hnn2 : (0:ℝ) ≤ ‖x - u‖ + R := add_nonneg (norm_nonneg _) hRnn
    have hsq1 : (‖x + u‖ + R) ^ 2 ≤ (‖x‖ + 1 + R) ^ 2 := by
      apply pow_le_pow_left₀ hnn1 _ 2
      linarith
    have hsq2 : (‖x - u‖ + R) ^ 2 ≤ (‖x‖ + 1 + R) ^ 2 := by
      apply pow_le_pow_left₀ hnn2 _ 2
      linarith
    have h_up : fderiv ℝ φ x u ≤ B x := by
      have h1 := hsub x u
      have h2 := hupper (x + u)
      have h3 := hlower x
      have h4 : (‖x + u‖ + R) ^ 2 / ε ^ 2 ≤ (‖x‖ + 1 + R) ^ 2 / ε ^ 2 :=
        div_le_div_of_nonneg_right hsq1 (by positivity)
      simp only [hB, hK]
      linarith
    have h_dn : -fderiv ℝ φ x u ≤ B x := by
      have h1 := hsub x (-u)
      rw [show fderiv ℝ φ x (-u) = -fderiv ℝ φ x u from by rw [map_neg]] at h1
      rw [show x + -u = x - u from by abel] at h1
      have h2 := hupper (x - u)
      have h3 := hlower x
      have h4 : (‖x - u‖ + R) ^ 2 / ε ^ 2 ≤ (‖x‖ + 1 + R) ^ 2 / ε ^ 2 :=
        div_le_div_of_nonneg_right hsq2 (by positivity)
      simp only [hB, hK]
      linarith
    rw [abs_le]
    exact ⟨by linarith, h_up⟩
  -- `B` is dominated by a quadratic polynomial.
  have hB_le : ∀ x, B x ≤ ((1 + R) ^ 2 / ε ^ 2 + max K 0) * (1 + ‖x‖) ^ 2 := by
    intro x
    have hn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
    have h1 : ‖x‖ + 1 + R ≤ (1 + R) * (1 + ‖x‖) := by
      nlinarith [mul_nonneg hRnn hn]
    have h1nn : (0:ℝ) ≤ ‖x‖ + 1 + R := by positivity
    have h2 : (‖x‖ + 1 + R) ^ 2 ≤ ((1 + R) * (1 + ‖x‖)) ^ 2 :=
      pow_le_pow_left₀ h1nn h1 2
    have h2' : (‖x‖ + 1 + R) ^ 2 ≤ (1 + R) ^ 2 * (1 + ‖x‖) ^ 2 := by
      calc (‖x‖ + 1 + R) ^ 2 ≤ ((1 + R) * (1 + ‖x‖)) ^ 2 := h2
        _ = (1 + R) ^ 2 * (1 + ‖x‖) ^ 2 := by ring
    have hA : (‖x‖ + 1 + R) ^ 2 / ε ^ 2 ≤ ((1 + R) ^ 2 / ε ^ 2) * (1 + ‖x‖) ^ 2 := by
      calc (‖x‖ + 1 + R) ^ 2 / ε ^ 2 ≤ ((1 + R) ^ 2 * (1 + ‖x‖) ^ 2) / ε ^ 2 :=
            div_le_div_of_nonneg_right h2' (by positivity)
        _ = ((1 + R) ^ 2 / ε ^ 2) * (1 + ‖x‖) ^ 2 := by ring
    have h4 : (1:ℝ) ≤ (1 + ‖x‖) ^ 2 := one_le_pow₀ (by linarith)
    have h5 : K ≤ max K 0 * (1 + ‖x‖) ^ 2 := by
      have hmax : 0 ≤ max K 0 := le_max_right K 0
      have hmul : max K 0 * 1 ≤ max K 0 * (1 + ‖x‖) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 hmax
      have hle : K ≤ max K 0 := le_max_left K 0
      nlinarith [hmul, hle, hmul]
    have h6 : ((1 + R) ^ 2 / ε ^ 2) * (1 + ‖x‖) ^ 2 + max K 0 * (1 + ‖x‖) ^ 2
        = ((1 + R) ^ 2 / ε ^ 2 + max K 0) * (1 + ‖x‖) ^ 2 := by ring
    simp only [hB, hK]
    calc (‖x‖ + 1 + R) ^ 2 / ε ^ 2 + K
        ≤ ((1 + R) ^ 2 / ε ^ 2) * (1 + ‖x‖) ^ 2 + max K 0 * (1 + ‖x‖) ^ 2 :=
          add_le_add hA h5
      _ = ((1 + R) ^ 2 / ε ^ 2 + max K 0) * (1 + ‖x‖) ^ 2 := h6
  -- Assemble: reduce arbitrary `v` to a unit direction.
  refine ⟨(1 + R) ^ 2 / ε ^ 2 + max K 0, by positivity, 2, fun x v => ?_⟩
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    set u : EuclideanSpace ℝ (Fin n) := ‖v‖⁻¹ • v with hu
    have hu_norm : ‖u‖ = 1 := by
      rw [hu, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        inv_mul_cancel₀ (ne_of_gt hnorm_pos)]
    have hv_eq : v = ‖v‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ (ne_of_gt hnorm_pos), one_smul]
    have hfder : fderiv ℝ φ x v = ‖v‖ * fderiv ℝ φ x u := by
      conv_lhs => rw [hv_eq]
      rw [map_smul, smul_eq_mul]
    rw [hfder, abs_mul, abs_of_nonneg (norm_nonneg v)]
    calc ‖v‖ * |fderiv ℝ φ x u| ≤ ‖v‖ * B x :=
          mul_le_mul_of_nonneg_left (hunit x u hu_norm) (norm_nonneg v)
      _ ≤ ‖v‖ * (((1 + R) ^ 2 / ε ^ 2 + max K 0) * (1 + ‖x‖) ^ 2) :=
          mul_le_mul_of_nonneg_left (hB_le x) (norm_nonneg v)
      _ = ((1 + R) ^ 2 / ε ^ 2 + max K 0) * (1 + ‖x‖) ^ 2 * ‖v‖ := by ring

end Commons.Analysis.Asymptotics
