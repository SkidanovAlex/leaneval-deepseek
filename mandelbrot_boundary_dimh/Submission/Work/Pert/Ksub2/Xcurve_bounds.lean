import Mathlib
import Submission.Work.Pert.Ksub2.Setup

/-!
# `Work.Pert.Ksub2.Xcurve_bounds`

Shishikura (arXiv math/9201282), Appendix A: the curve `u ↦ Xc d u = τ₀ (φ₀ u)` of a `§4.1`-datum
`d` is asymptotically the identity, with a logarithmic error, together with a derivative estimate.

The whole content is the two-term asymptotic of the Fatou coordinate in the repelling sector,
`φ_asymp : τ₀ (φ₀ w) = w + a log(-w) + b + o(1)` (`‖w‖ → ∞` in `QLeft ξ₀`):

* the *value* bound `‖Xc d u - u‖ ≤ C (1 + log ‖u‖)` uses the asymptotic at the single point `u`
  (with the fixed error `ε = 1`), the elementary bound `‖log(-u)‖ ≤ log ‖u‖ + π`, and the fact that
  the error of the asymptotic is absorbed by `C (1 + log ‖u‖)` for a large enough `C`;
* the *derivative* bound `‖deriv (Xc d) u - 1‖ ≤ C (1 + log ‖u‖) / ‖u‖` is Cauchy's estimate
  applied to `g = Xc d - id` on the disc of radius `‖u‖/20` around `u`: on that disc
  `‖g‖ ≤ 1 + ‖a log(-w) + b‖ ≤ C (1 + log ‖u‖)`, so `‖g' u‖ ≤ 20 · sup‖g‖ / ‖u‖`.

The disc of radius `‖u‖/20` lies in the ball of radius `‖u‖/10` of the hypothesis, hence in
`QLeft ξ₀ ⊆ Dφ`; there `φ` is holomorphic and — since the asymptotic forces `τ₀ (φ w) ≠ 0` for
`‖w‖` large — nonvanishing, so `g` is holomorphic and Cauchy's estimate applies.
-/

namespace Work.Pert.Ksub2

open Complex Metric

theorem Xcurve_bounds {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, u ∈ MandelDim.QLeft d.ξ₀ → C ≤ ‖u‖ →
      Metric.ball u (‖u‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ →
      ‖Work.Pert.Xc d u - u‖ ≤ C * (1 + Real.log ‖u‖) ∧
      ‖deriv (Work.Pert.Xc d) u - 1‖ ≤ C * (1 + Real.log ‖u‖) / ‖u‖ := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨R_A, hR_A⟩ := hasym 1 one_pos
  obtain ⟨R_B, hR_B⟩ := Work.Pert.exists_norm_add_clog_bound a b 1 one_pos
  set KK : ℝ := ‖a‖ with hKK
  set LL : ℝ := ‖b‖ with hLL
  set Rv : ℝ := max R_B (R_A + 1) with hRv
  set M₀ : ℝ := 1 + KK * Real.pi + KK * Real.log (11 / 10 : ℝ) + LL + KK + 1 with hM₀
  set C₀ : ℝ := 100 * (M₀ + max Rv 1 + 1) with hC₀
  have hKK0 : 0 ≤ KK := by rw [hKK]; exact norm_nonneg a
  have hLL0 : 0 ≤ LL := by rw [hLL]; exact norm_nonneg b
  have hlog1110 : 0 ≤ Real.log (11 / 10 : ℝ) := Real.log_nonneg (by norm_num)
  have hkp : 0 ≤ KK * Real.pi := mul_nonneg hKK0 Real.pi_pos.le
  have hkl : 0 ≤ KK * Real.log (11 / 10 : ℝ) := mul_nonneg hKK0 hlog1110
  have hM0_0 : 0 ≤ M₀ := by rw [hM₀]; linarith
  have hRv1 : (1 : ℝ) ≤ max Rv 1 := le_max_right _ _
  have hC₀exp : C₀ = 100 * M₀ + 100 * max Rv 1 + 100 := by rw [hC₀]; ring
  have hC₀div20 : C₀ / 20 = 5 * M₀ + 5 * max Rv 1 + 5 := by rw [hC₀]; ring
  have hC₀pos : 0 < C₀ := by rw [hC₀exp]; linarith
  have hC₀20 : (20 : ℝ) ≤ C₀ := by rw [hC₀exp]; linarith
  have hC₀M20 : M₀ ≤ C₀ / 20 := by rw [hC₀div20]; linarith
  have hC₀Rv : max Rv 1 ≤ C₀ := by rw [hC₀exp]; linarith
  have hC₀1 : 1 + KK * Real.pi + LL ≤ C₀ := by
    have h1 : 1 + KK * Real.pi + LL ≤ M₀ := by rw [hM₀]; linarith
    linarith
  have hC₀KK : KK ≤ C₀ := by
    have h1 : KK ≤ M₀ := by rw [hM₀]; linarith
    linarith
  have hC₀div1 : 1 + KK * Real.pi + KK * Real.log (11 / 10 : ℝ) + LL ≤ C₀ / 20 := by
    have h1 : 1 + KK * Real.pi + KK * Real.log (11 / 10 : ℝ) + LL ≤ M₀ := by rw [hM₀]; linarith
    linarith
  have hC₀divKK : KK ≤ C₀ / 20 := by
    have h1 : KK ≤ M₀ := by rw [hM₀]; linarith
    linarith
  have hRA1 : R_A + 1 ≤ Rv := by rw [hRv]; exact le_max_right _ _
  have hRB_le : R_B ≤ Rv := by rw [hRv]; exact le_max_left _ _
  refine ⟨C₀, hC₀pos, fun u huQ hCu hball => ⟨?_, ?_⟩⟩
  · -- value bound
    have hu_ge1 : (1 : ℝ) ≤ ‖u‖ := le_trans (by linarith) hCu
    have hlogu0 : 0 ≤ Real.log ‖u‖ := Real.log_nonneg hu_ge1
    have hufar : R_A < ‖u‖ := by
      have h1 : R_A + 1 ≤ max Rv 1 := le_trans hRA1 (le_max_left Rv 1)
      linarith
    have hasy := hR_A u huQ hufar
    have hlog_neg : ‖Complex.log (-u)‖ ≤ Real.log ‖u‖ + Real.pi := by
      have h := Work.Pert.norm_clog_le (-u)
      rw [norm_neg, abs_of_nonneg hlogu0] at h
      exact h
    have hlin : ‖a * Complex.log (-u) + b‖ ≤ KK * Real.log ‖u‖ + KK * Real.pi + LL := by
      calc ‖a * Complex.log (-u) + b‖ ≤ ‖a * Complex.log (-u)‖ + ‖b‖ := norm_add_le _ _
        _ = KK * ‖Complex.log (-u)‖ + LL := by rw [norm_mul, hKK, hLL]
        _ ≤ KK * (Real.log ‖u‖ + Real.pi) + LL := by
              have h := mul_le_mul_of_nonneg_left hlog_neg hKK0
              linarith
        _ = KK * Real.log ‖u‖ + KK * Real.pi + LL := by ring
    have hsplit : Work.Pert.Xc d u - u =
        (MandelDim.tau0 (d.φ u) - (u + a * Complex.log (-u) + b)) +
          (a * Complex.log (-u) + b) := by
      simp only [Work.Pert.Xc]
      ring
    rw [hsplit]
    have htri : ‖(MandelDim.tau0 (d.φ u) - (u + a * Complex.log (-u) + b)) +
        (a * Complex.log (-u) + b)‖ ≤
        ‖MandelDim.tau0 (d.φ u) - (u + a * Complex.log (-u) + b)‖ +
          ‖a * Complex.log (-u) + b‖ := norm_add_le _ _
    have hce : C₀ * (1 + Real.log ‖u‖) = C₀ + C₀ * Real.log ‖u‖ := by ring
    have hkl' : KK * Real.log ‖u‖ ≤ C₀ * Real.log ‖u‖ :=
      mul_le_mul_of_nonneg_right hC₀KK hlogu0
    rw [hce]
    linarith [htri, hasy, hlin, hC₀1, hkl']
  · -- derivative bound
    have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le hC₀pos hCu
    have hu_ge1 : (1 : ℝ) ≤ ‖u‖ := le_trans (by linarith) hCu
    have hlogu0 : 0 ≤ Real.log ‖u‖ := Real.log_nonneg hu_ge1
    have h9C : 18 * max Rv 1 ≤ 9 * C₀ / 10 := by
      have he : 9 * C₀ / 10 = 90 * M₀ + 90 * max Rv 1 + 90 := by rw [hC₀]; ring
      rw [he]; linarith
    have hphi_ne : ∀ w ∈ Metric.ball u (‖u‖ / 10), d.φ w ≠ 0 := by
      intro w hw hzero
      have hwQ : w ∈ MandelDim.QLeft d.ξ₀ := hball hw
      have hwn : 9 * ‖u‖ / 10 ≤ ‖w‖ := by
        have h1 : dist w u < ‖u‖ / 10 := Metric.mem_ball.mp hw
        rw [dist_eq_norm] at h1
        have h2 : ‖u‖ ≤ ‖u - w‖ + ‖w‖ := by
          have h := norm_add_le (u - w) w
          rwa [sub_add_cancel] at h
        have h3 : ‖u - w‖ = ‖w - u‖ := norm_sub_rev u w
        have h4 : ‖w - u‖ = dist w u := by rw [dist_eq_norm]
        linarith
      have hwbig : max Rv 1 ≤ ‖w‖ := by
        have h3 : 9 * C₀ / 10 ≤ 9 * ‖u‖ / 10 := by linarith
        have h4 : max Rv 1 ≤ 18 * max Rv 1 := by linarith
        linarith
      have hwRA : R_A < ‖w‖ := by
        have h1 : R_A + 1 ≤ max Rv 1 := le_trans hRA1 (le_max_left Rv 1)
        linarith
      have hwRB : R_B ≤ ‖w‖ := by
        have h1 : R_B ≤ max Rv 1 := le_trans hRB_le (le_max_left Rv 1)
        linarith
      have h1 := hR_A w hwQ hwRA
      have h2 := hR_B w hwRB
      have hz : MandelDim.tau0 (d.φ w) = 0 := by rw [hzero]; simp [MandelDim.tau0]
      rw [hz, zero_sub, norm_neg] at h1
      linarith
    have hφd : DifferentiableOn ℂ d.φ (Metric.ball u (‖u‖ / 10)) :=
      d.φ_holo.mono (fun w hw => d.Q_sub (hball hw))
    have hτ : DifferentiableOn ℂ MandelDim.tau0 ({0}ᶜ : Set ℂ) :=
      (differentiableOn_const (-1 : ℂ)).div differentiableOn_id (fun z hz => hz)
    have hXcd : DifferentiableOn ℂ (Work.Pert.Xc d) (Metric.ball u (‖u‖ / 10)) :=
      hτ.comp hφd (fun w hw => by simpa using hphi_ne w hw)
    have hgd : DifferentiableOn ℂ (fun w : ℂ => Work.Pert.Xc d w - w)
        (Metric.ball u (‖u‖ / 10)) := by
      have h := hXcd.sub differentiableOn_id
      rw [show (fun w : ℂ => Work.Pert.Xc d w - w) = ((Work.Pert.Xc d) - id : ℂ → ℂ) from rfl]
      exact h
    have hdc : DiffContOnCl ℂ (fun w : ℂ => Work.Pert.Xc d w - w) (Metric.ball u (‖u‖ / 20)) :=
      hgd.diffContOnCl_ball (Metric.closedBall_subset_ball (by linarith))
    set M : ℝ := 1 + (KK * Real.log ‖u‖ + KK * Real.log (11 / 10 : ℝ) + KK * Real.pi) + LL with hM
    have hsphere : ∀ z ∈ Metric.sphere u (‖u‖ / 20), ‖Work.Pert.Xc d z - z‖ ≤ M := by
      intro z hz
      rw [Metric.mem_sphere, dist_eq_norm] at hz
      have hzn_ge : 19 * ‖u‖ / 20 ≤ ‖z‖ := by
        have h1 : ‖u‖ ≤ ‖u - z‖ + ‖z‖ := by
          have h := norm_add_le (u - z) z
          rwa [sub_add_cancel] at h
        have h2 : ‖u - z‖ = ‖z - u‖ := norm_sub_rev u z
        linarith
      have hzball : z ∈ Metric.ball u (‖u‖ / 10) := by
        rw [Metric.mem_ball, dist_eq_norm]; linarith
      have hzQ : z ∈ MandelDim.QLeft d.ξ₀ := hball hzball
      have hzbig : max Rv 1 ≤ ‖z‖ := by
        have h3 : 9 * C₀ / 10 ≤ 9 * ‖u‖ / 10 := by linarith
        have h4 : max Rv 1 ≤ 18 * max Rv 1 := by linarith
        linarith
      have hzRA : R_A < ‖z‖ := by
        have h1 : R_A + 1 ≤ max Rv 1 := le_trans hRA1 (le_max_left Rv 1)
        linarith
      have hzge1 : (1 : ℝ) ≤ ‖z‖ := by linarith
      have hzlog : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hzge1
      have hasyz := hR_A z hzQ hzRA
      have hlogz : ‖Complex.log (-z)‖ ≤ Real.log ‖z‖ + Real.pi := by
        have h := Work.Pert.norm_clog_le (-z)
        rw [norm_neg, abs_of_nonneg hzlog] at h
        exact h
      have hlz : ‖a * Complex.log (-z) + b‖ ≤ KK * Real.log ‖z‖ + KK * Real.pi + LL := by
        calc ‖a * Complex.log (-z) + b‖ ≤ ‖a * Complex.log (-z)‖ + ‖b‖ := norm_add_le _ _
          _ = KK * ‖Complex.log (-z)‖ + LL := by rw [norm_mul, hKK, hLL]
          _ ≤ KK * (Real.log ‖z‖ + Real.pi) + LL := by
                have h := mul_le_mul_of_nonneg_left hlogz hKK0
                linarith
          _ = KK * Real.log ‖z‖ + KK * Real.pi + LL := by ring
      have hsplit : Work.Pert.Xc d z - z =
          (MandelDim.tau0 (d.φ z) - (z + a * Complex.log (-z) + b)) +
            (a * Complex.log (-z) + b) := by
        simp only [Work.Pert.Xc]; ring
      have h1 : ‖Work.Pert.Xc d z - z‖ ≤ 1 + (KK * Real.log ‖z‖ + KK * Real.pi + LL) := by
        rw [hsplit]
        have htri := norm_add_le (MandelDim.tau0 (d.φ z) - (z + a * Complex.log (-z) + b))
          (a * Complex.log (-z) + b)
        linarith [htri, hasyz, hlz]
      have hzn_le : ‖z‖ ≤ (11 / 10 : ℝ) * ‖u‖ := by
        have h1 : ‖z‖ ≤ ‖z - u‖ + ‖u‖ := by
          have h := norm_add_le (z - u) u
          rwa [sub_add_cancel] at h
        linarith
      have h2 : Real.log ‖z‖ ≤ Real.log ‖u‖ + Real.log (11 / 10 : ℝ) := by
        calc Real.log ‖z‖ ≤ Real.log ((11 / 10 : ℝ) * ‖u‖) :=
              Real.log_le_log (by linarith) hzn_le
          _ = Real.log (11 / 10 : ℝ) + Real.log ‖u‖ :=
              Real.log_mul (by norm_num) (ne_of_gt hu_pos)
          _ = Real.log ‖u‖ + Real.log (11 / 10 : ℝ) := by ring
      have h3 : KK * Real.log ‖z‖ ≤ KK * Real.log ‖u‖ + KK * Real.log (11 / 10 : ℝ) := by
        have h := mul_le_mul_of_nonneg_left h2 hKK0
        rwa [mul_add] at h
      rw [hM]
      linarith [h1, h3]
    have hcauchy : ‖deriv (fun w : ℂ => Work.Pert.Xc d w - w) u‖ ≤ M / (‖u‖ / 20) :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun w : ℂ => Work.Pert.Xc d w - w)
        (c := u) (R := ‖u‖ / 20) (C := M) (by linarith) hdc hsphere
    have hMbound : 20 * M ≤ C₀ * (1 + Real.log ‖u‖) := by
      have hkey : 20 * M = 20 * (1 + KK * Real.pi + KK * Real.log (11 / 10 : ℝ) + LL) +
          20 * (KK * Real.log ‖u‖) := by rw [hM]; ring
      have h20 : 20 * (1 + KK * Real.pi + KK * Real.log (11 / 10 : ℝ) + LL) ≤ C₀ := by
        linarith [hC₀div1]
      have hk : 20 * KK ≤ C₀ := by linarith [hC₀divKK]
      have hB : 20 * (KK * Real.log ‖u‖) ≤ C₀ * Real.log ‖u‖ := by nlinarith [hk, hlogu0]
      have hce : C₀ * (1 + Real.log ‖u‖) = C₀ + C₀ * Real.log ‖u‖ := by ring
      rw [hkey, hce]
      linarith [h20, hB]
    have hstep : M / (‖u‖ / 20) ≤ C₀ * (1 + Real.log ‖u‖) / ‖u‖ := by
      have h1 : M / (‖u‖ / 20) = 20 * M / ‖u‖ := by rw [div_div_eq_mul_div, mul_comm]
      rw [h1]
      exact (div_le_div_iff_of_pos_right hu_pos).mpr (by linarith [hMbound])
    have hdX : DifferentiableAt ℂ (Work.Pert.Xc d) u :=
      hXcd.differentiableAt (Metric.ball_mem_nhds u (by linarith))
    have hdsub : deriv (fun w : ℂ => Work.Pert.Xc d w - w) u = deriv (Work.Pert.Xc d) u - 1 := by
      have hh := deriv_sub hdX differentiableAt_id
      rw [show (fun w : ℂ => Work.Pert.Xc d w - w) = ((Work.Pert.Xc d) - id : ℂ → ℂ) from rfl]
      simpa [deriv_id] using hh
    have hone : deriv (Work.Pert.Xc d) u - 1 = deriv (fun w : ℂ => Work.Pert.Xc d w - w) u :=
      hdsub.symm
    rw [hone]
    linarith [hcauchy, hstep]

end Work.Pert.Ksub2
