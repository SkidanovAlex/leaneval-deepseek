import Mathlib
import Submission.Commons.Analysis.Complex.zeroFactor_g
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Commons.Analysis.Complex.Harmonic.annulus_strong_max
import Submission.Commons.Analysis.Complex.borelCaratheodory_deriv_le
import Submission.Commons.Analysis.Complex.divisor_subBall_factor

noncomputable section

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Real Topology BigOperators

namespace Commons.Analysis.Complex

private lemma sub_zpow_diffAt {u x : ℂ} {n : ℤ} (hn : 0 ≤ n) :
    DifferentiableAt ℂ (fun z : ℂ => (z - u) ^ n) x := by
  have hlin : DifferentiableAt ℂ (fun z : ℂ => z - u) x := by fun_prop
  exact hlin.zpow (Or.inr hn)

/-- **Log-derivative decomposition** at an interior point `s` (inside the factorization ball):
`logDeriv f s = (∑ᶠ u divisor(u)/(s−u)) + logDeriv g s`, where `g` is the zero-free factor of
the canonical factorization with the half-ball divisor. -/
private lemma logDeriv_decompose_subBall {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hfac : ∀ z : ℂ, z ∈ Metric.closedBall c R →
      f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall c (R / 2))) u : ℤ)) * g z)
    {s : ℂ} (hsB : s ∈ Metric.ball c R) (hfs : f s ≠ 0)
    (hgdiff : DifferentiableAt ℂ g s) (hg0 : g s ≠ 0) :
    logDeriv f s =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall c (R / 2))) u : ℤ) : ℂ) *
        (1 / (s - u))) + logDeriv g s := by
  classical
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall c (R / 2)) u
  let P : ℂ → ℂ := fun z => ∏ᶠ u : ℂ, (z - u) ^ (d u)
  have hfB : AnalyticOnNhd ℂ f (Metric.closedBall c R) := hf
  have hsub : Metric.closedBall c (R / 2) ⊆ Metric.closedBall c R := by
    intro z hz
    have hzle : ‖z - c‖ ≤ R / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hleR : R / 2 ≤ R := by linarith
    linarith
  have hf_inner : AnalyticOnNhd ℂ f (Metric.closedBall c (R / 2)) := hfB.mono hsub
  have hsupp : (support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall c (R / 2))
      hfB.meromorphicOn (isCompact_closedBall c R) hsub
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf_inner) u
  have hds : d s = 0 := by
    dsimp [d]
    by_cases hs_inner : s ∈ Metric.closedBall c (R / 2)
    · rw [MeromorphicOn.divisor_apply hf_inner.meromorphicOn hs_inner]
      have hord : meromorphicOrderAt f s = 0 :=
        meromorphicOrderAt_eq_zero_of_ne_zero (hf_inner s hs_inner) hfs
      simp [hord]
    · rw [MeromorphicOn.divisor_def]
      simp [hs_inner]
  let S : Finset ℂ := hsupp.toFinset
  have hS_coe : (S : Set ℂ) = support d := by
    exact hsupp.coe_toFinset
  have hP_fun : P = (fun z : ℂ => ∏ u ∈ S, (z - u) ^ (d u)) := by
    funext z
    dsimp [P, S]
    have hsub2 : mulSupport (fun u : ℂ => (z - u) ^ (d u)) ⊆ (hsupp.toFinset : Set ℂ) := by
      intro u hu
      have hd_ne : d u ≠ 0 := by
        intro hd0
        have : (z - u) ^ (d u) = 1 := by simp [hd0]
        exact hu this
      exact hsupp.mem_toFinset.mpr hd_ne
    rw [finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (z - u) ^ (d u)) hsub2]
  have hfac0 : ∀ u ∈ S, (s - u) ^ (d u) ≠ 0 := by
    intro u hu
    have hd_ne : d u ≠ 0 := by
      have huS : u ∈ (S : Set ℂ) := by simpa using hu
      rw [hS_coe] at huS
      exact huS
    have hs_ne : s ≠ u := by
      intro h
      have : d s = d u := by rw [h]
      exact hd_ne (by simpa [hds] using this.symm)
    exact zpow_ne_zero (d u) (sub_ne_zero.mpr hs_ne)
  have hdiff : ∀ u ∈ S, DifferentiableAt ℂ (fun z : ℂ => (z - u) ^ (d u)) s := by
    intro u hu
    exact sub_zpow_diffAt (hd_nonneg u)
  have hdiffP : DifferentiableAt ℂ P s := by
    rw [hP_fun]
    exact DifferentiableAt.fun_finsetProd (u := S) (f := fun u z : ℂ => (z - u) ^ (d u)) (x := s) hdiff
  have hs_cbR : s ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hsB
  have hfPg : f s = P s * g s := by
    simpa [P, d] using (hfac s hs_cbR)
  have hP0 : P s ≠ 0 := by
    intro hP0
    apply hfs
    rw [hfPg, hP0, zero_mul]
  have hPg_eq_f : (fun z : ℂ => P z * g z) =ᶠ[𝓝 s] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hsB] with z hz
    simpa [P, d] using (hfac z (Metric.ball_subset_closedBall hz)).symm
  have hL2 : logDeriv f s = logDeriv (fun z : ℂ => P z * g z) s := by
    have hdv : deriv (fun z : ℂ => P z * g z) s = deriv f s := hPg_eq_f.deriv_eq
    rw [logDeriv_apply, logDeriv_apply]
    rw [← hdv]
    rw [hfPg]
  have hlogP : logDeriv P s = ∑ u ∈ S, (d u : ℂ) * (1 / (s - u)) := by
    calc
      logDeriv P s = logDeriv (fun z : ℂ => ∏ u ∈ S, (z - u) ^ (d u)) s := by
        rw [hP_fun]
      _ = ∑ u ∈ S, logDeriv (fun z : ℂ => (z - u) ^ (d u)) s := by
        exact logDeriv_fun_prod hfac0 hdiff
      _ = ∑ u ∈ S, (d u : ℂ) * (1 / (s - u)) := by
        apply Finset.sum_congr rfl
        intro u hu
        calc
          logDeriv (fun z : ℂ => (z - u) ^ (d u)) s = (d u : ℂ) * logDeriv (fun z : ℂ => z - u) s := by
            exact logDeriv_fun_zpow (by fun_prop) (d u)
          _ = (d u : ℂ) * (1 / (s - u)) := by
            congr 1
            rw [logDeriv_apply]
            rw [deriv_sub_const u]
            simp
  have hL3 : logDeriv (fun z : ℂ => P z * g z) s = logDeriv P s + logDeriv g s := by
    exact logDeriv_fun_mul s hP0 hg0 hdiffP hgdiff
  have hfin_sum : (∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * (1 / (s - u)))) =
      ∑ u ∈ S, (((d u : ℤ) : ℂ) * (1 / (s - u))) := by
    rw [finsum_eq_sum_of_support_subset (fun u : ℂ => (((d u : ℤ) : ℂ) * (1 / (s - u)))) (s := S) ?_]
    · intro u hu
      have hd_ne : d u ≠ 0 := by
        intro hd0
        have : ((d u : ℤ) : ℂ) * (1 / (s - u)) = 0 := by simp [hd0]
        exact hu this
      rw [hS_coe]
      exact hd_ne
  rw [hfin_sum]
  calc
    logDeriv f s = logDeriv P s + logDeriv g s := by
      rw [hL2, hL3]
    _ = (∑ u ∈ S, (d u : ℂ) * (1 / (s - u))) + logDeriv g s := by
      rw [hlogP]

theorem logDeriv_sub_divisor_le {f : ℂ → ℂ} {c : ℂ} {R A α : ℝ}
    (hR : 0 < R) (hA1 : (1 : ℝ) ≤ A) (hα0 : 0 ≤ α) (hα : α < 1 / 2)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hfc : f c ≠ 0)
    (hcirc_out : ∀ w : ℂ, ‖w - c‖ = R → f w ≠ 0)
    (hcirc_in : ∀ w : ℂ, ‖w - c‖ = R / 2 → f w ≠ 0)
    (hAb : ∀ w : ℂ, ‖w - c‖ = R → ‖f w‖ ≤ A * ‖f c‖)
    {s : ℂ} (hs : ‖s - c‖ ≤ α * R) (hfs : f s ≠ 0) :
    ‖logDeriv f s -
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall c (R / 2))) u : ℤ) : ℂ) *
          (1 / (s - u)))‖ ≤
      4 * Real.log A / (R * (1 - 2 * α) ^ 2) := by
  classical
  rcases divisor_subBall_factor (hR := hR) (hA1 := hA1) (hf := hf) (hfc := hfc)
    (hcirc_out := hcirc_out) (hcirc_in := hcirc_in) (hAb := hAb) with
    ⟨g, hg_an, hfac, hg_nz, hg_le, hgc0⟩
  have hR2 : 0 < R / 2 := by positivity
  have hαR0 : 0 ≤ α * R := mul_nonneg hα0 (le_of_lt hR)
  have hαlt : α * R < R / 2 := by
    have hαR : α * R < (1 / 2) * R := mul_lt_mul_of_pos_right hα hR
    nlinarith [hαR0]
  have hs_ball : s ∈ Metric.ball c (R / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hs hαlt
  have hg_an_ball : AnalyticOnNhd ℂ g (Metric.ball c (R / 2)) := by
    intro z hz
    have hzmem : z ∈ Metric.closedBall c R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hle : ‖z - c‖ ≤ R / 2 := le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
      have hleR : R / 2 ≤ R := by linarith
      linarith
    exact hg_an z hzmem
  have hg_nz_ball : ∀ w : ℂ, w ∈ Metric.ball c (R / 2) → g w ≠ 0 := by
    intro w hw
    exact hg_nz w (Metric.ball_subset_closedBall hw)
  have hgs : g s ≠ 0 := hg_nz_ball s hs_ball
  have hs_cb : s ∈ Metric.closedBall c R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hle2 : α * R ≤ R / 2 := le_of_lt hαlt
    linarith
  have hs_ballR : s ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hlt : α * R < R := by
      have hlt2 : α * R < R / 2 := hαlt
      linarith
    exact lt_of_le_of_lt hs hlt
  have hgdiff_s : DifferentiableAt ℂ g s := (hg_an s hs_cb).differentiableAt
  have hdec := logDeriv_decompose_subBall (f := f) (g := g) (c := c) (R := R) hR hf hfac hs_ballR hfs hgdiff_s hgs
  rcases logPrimitiveOnBall_analytic (g := g) (c := c) (R := R / 2) hg_an_ball hR2 hg_nz_ball with
    ⟨F, hFd, hFh, hFc_re, hFre⟩
  let H : ℂ → ℂ := fun z => F z - F c
  have hHc : H c = 0 := by simp [H]
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hRe_le : ∀ w : ℂ, w ∈ Metric.ball c (R / 2) → (H w).re ≤ Real.log A := by
    intro w hw
    have hw_cb_R : w ∈ Metric.closedBall c R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hle : ‖w - c‖ ≤ R / 2 := le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
      have hleR : R / 2 ≤ R := by linarith
      linarith
    have hgw : ‖g w‖ ≤ A * ‖g c‖ := hg_le w hw_cb_R
    have hlog : Real.log ‖g w‖ ≤ Real.log (A * ‖g c‖) := by
      have hpos1 : 0 < ‖g w‖ := norm_pos_iff.mpr (hg_nz_ball w hw)
      have hpos2 : 0 < A * ‖g c‖ := mul_pos (lt_of_lt_of_le zero_lt_one hA1) (norm_pos_iff.mpr hgc0)
      exact Real.log_le_log hpos1 hgw
    calc
      (H w).re = (F w).re - (F c).re := by simp [H, sub_re]
      _ = Real.log ‖g w‖ - Real.log ‖g c‖ := by rw [hFre w hw, hFc_re]
      _ ≤ Real.log (A * ‖g c‖) - Real.log ‖g c‖ := by linarith
      _ = Real.log A := by
        rw [Real.log_mul (by linarith : (A : ℝ) ≠ 0) (norm_ne_zero_iff.mpr hgc0)]
        ring
  have hF_an : AnalyticOnNhd ℂ F (Metric.ball c (R / 2)) :=
    hFd.analyticOnNhd (Metric.isOpen_ball : IsOpen (Metric.ball c (R / 2)))
  have hH_an : AnalyticOnNhd ℂ H (Metric.ball c (R / 2)) := by
    have hHd : DifferentiableOn ℂ H (Metric.ball c (R / 2)) := by
      intro z hz
      exact ((hF_an z hz).differentiableAt.sub_const (F c)).differentiableWithinAt
    exact hHd.analyticOnNhd (Metric.isOpen_ball : IsOpen (Metric.ball c (R / 2)))
  have hb := borelCaratheodory_deriv_le (F := H) (c := c) (R := R / 2) (B := Real.log A)
    hR2 hlogA0 hH_an hHc hRe_le s hs_ball
  have hderivH : deriv H s = logDeriv g s := by
    have hFder : deriv F s = deriv g s / g s := (hFh s hs_ball).deriv
    calc
      deriv H s = deriv F s := by simp [H]
      _ = deriv g s / g s := hFder
      _ = logDeriv g s := rfl
  have hmain : ‖logDeriv g s‖ ≤ 4 * Real.log A / (R * (1 - 2 * α) ^ 2) := by
    have ha_pos : 0 < (R / 2) - ‖s - c‖ := by
      exact sub_pos.mpr (lt_of_le_of_lt hs hαlt)
    have hden_pos : 0 < R * (1 - 2 * α) ^ 2 := by
      have h12 : 0 < 1 - 2 * α := by nlinarith
      have hs0 : 0 < (1 - 2 * α) ^ 2 := sq_pos_of_pos h12
      positivity
    have hge : R * (1 - 2 * α) / 2 ≤ (R / 2) - ‖s - c‖ := by
      have h1 : ‖s - c‖ ≤ α * R := hs
      have hR0 : 0 ≤ R := le_of_lt hR
      nlinarith
    have hb1 : 0 ≤ (R / 2) - ‖s - c‖ := le_of_lt ha_pos
    have hb2 : 0 ≤ R * (1 - 2 * α) / 2 := by
      have h12 : 0 < 1 - 2 * α := by linarith
      positivity
    have hsq : (R * (1 - 2 * α) / 2) ^ 2 ≤ ((R / 2) - ‖s - c‖) ^ 2 := by
      exact (sq_le_sq₀ hb2 hb1).mpr hge
    calc
      ‖logDeriv g s‖ = ‖deriv H s‖ := by rw [← hderivH]
      _ ≤ 2 * (R / 2) * Real.log A / ((R / 2) - ‖s - c‖) ^ 2 := hb
      _ = R * Real.log A / ((R / 2) - ‖s - c‖) ^ 2 := by ring
      _ ≤ 4 * Real.log A / (R * (1 - 2 * α) ^ 2) := by
        by_cases hL0 : Real.log A = 0
        · simp [hL0]
        · have hLpos : 0 < Real.log A := lt_of_le_of_ne hlogA0 (Ne.symm hL0)
          rw [div_le_div_iff₀ (sq_pos_of_pos ha_pos) hden_pos]
          have hsq4 : R ^ 2 * (1 - 2 * α) ^ 2 ≤ 4 * ((R / 2) - ‖s - c‖) ^ 2 := by
            nlinarith [hsq]
          nlinarith
  calc
    ‖logDeriv f s - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall c (R / 2))) u : ℤ) : ℂ) *
          (1 / (s - u)))‖
        = ‖logDeriv g s‖ := by
          rw [hdec]
          simp only [add_sub_cancel_left]
      _ ≤ 4 * Real.log A / (R * (1 - 2 * α) ^ 2) := hmain
