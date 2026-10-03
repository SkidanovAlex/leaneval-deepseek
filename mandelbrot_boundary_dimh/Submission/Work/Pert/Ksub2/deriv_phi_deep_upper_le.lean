import Mathlib
import Submission.Work.Pert.Ksub2.deriv_phi_deep_upper
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.phi_ne_zero_far

/-!
# `Work.Pert.Ksub2.deriv_phi_deep_upper_le`

The **sharp** form of the uniform upper bound for `‖deriv φ₀‖` on the deep part of Shishikura's
repelling sector, with the *explicit* constant `4 * (1 + 2 C₀)`.

`deriv_phi_deep_upper` produces *some* constant `C`, namely `(1 + 2C₀) * (4/R²)`, which is
useless for the perturbation argument (`Ksub_phi_close_v2`), where the final `δ`/`ε` thresholds are
compared with `C`.  The observation here is that on the deep region `-Re z ≥ R` with `R ≥ 1` one
has `‖z‖ ≥ 1`, so the *crude* product bound

  `‖deriv φ₀ z‖ = ‖deriv (Xc d) z‖ · ‖φ₀ z‖² ≤ (1 + 2C₀) · (2/‖z‖)² ≤ 4 (1 + 2C₀)`

already gives the constant `4 (1 + 2C₀)`, independent of the depth `R`, and this is exactly what
the caller needs.  All the constants (`C₀`, `R₁`, `RL`) are hypotheses here, so the statement is
self-contained and does not depend on the existential forms of `Xcurve_bounds`,
`phi_ne_zero_far` or the `log = o(id)` estimate.
-/

namespace Work.Pert.Ksub2

open Complex Metric Filter

/-- `‖τ₀ w‖ = 1/‖w‖` (`τ₀ w = -1/w`). -/
private lemma norm_tau0_le (w : ℂ) : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by
  simp [MandelDim.tau0, norm_neg, norm_one]

theorem deriv_phi_deep_upper_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {C₀ R₁ RL Bz : ℝ}
    (hC₀ : 0 < C₀)
    (hXc : ∀ z : ℂ, z ∈ MandelDim.QLeft d.ξ₀ → C₀ ≤ ‖z‖ →
      Metric.ball z (‖z‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ →
      ‖Work.Pert.Xc d z - z‖ ≤ C₀ * (1 + Real.log ‖z‖) ∧
      ‖deriv (Work.Pert.Xc d) z - 1‖ ≤ C₀ * (1 + Real.log ‖z‖) / ‖z‖)
    (hzero : ∀ w : ℂ, w ∈ MandelDim.QLeft d.ξ₀ → R₁ ≤ ‖w‖ →
      Metric.ball w (‖w‖ / 4) ⊆ MandelDim.QLeft d.ξ₀ →
      ∀ u ∈ Metric.ball w (‖w‖ / 4), d.φ u ≠ 0)
    (hRL : ∀ x : ℝ, RL ≤ x → C₀ * (1 + Real.log x) ≤ x / 2)
    (hBz : 0 ≤ Bz) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ C ≤ 4 * (1 + 2 * C₀) ∧
      ∀ z : ℂ, z ∈ d.Dφ → R ≤ -z.re → |z.im| ≤ Bz → ‖deriv d.φ z‖ ≤ C := by
  -- the depth threshold: large relative to the datum, the constants and `Bz`
  have hev : ∀ᶠ R : ℝ in Filter.atTop,
      d.ξ₀ + 1 ≤ R ∧ C₀ + 1 ≤ R ∧ RL ≤ R ∧ R₁ ≤ R ∧ 1 ≤ R ∧
        (4 * d.ξ₀ + Bz) / 3 + 1 ≤ R := by
    filter_upwards [Filter.eventually_ge_atTop (d.ξ₀ + 1), Filter.eventually_ge_atTop (C₀ + 1),
      Filter.eventually_ge_atTop RL, Filter.eventually_ge_atTop R₁,
      Filter.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_ge_atTop ((4 * d.ξ₀ + Bz) / 3 + 1)] with R h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨hRξ, hRC, hRLR, hR1R, hRone, hRbig⟩ := hR R le_rfl
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hRone
  refine ⟨R, 4 * (1 + 2 * C₀), hRpos, by linarith, le_rfl, ?_⟩
  intro z hz hzre hzim
  -- `z` is deep and to the left
  have hznorm : R ≤ ‖z‖ := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h2 : |z.re| = -z.re := abs_of_nonpos (by linarith)
    linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hRpos hznorm
  have hznorm1 : (1 : ℝ) ≤ ‖z‖ := le_trans hRone hznorm
  have hnormle : ‖z‖ ≤ -z.re + Bz := by
    have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have h2 : |z.re| = -z.re := abs_of_nonpos (by linarith)
    linarith
  have hzlt : z.re < -d.ξ₀ := by linarith [hRξ, hzre]
  have hzQ : z ∈ MandelDim.QLeft d.ξ₀ := Work.Parab.halfplane_subset_QLeft d.ξ₀ hzlt
  have hre_lt : z.re + ‖z‖ / 4 < -d.ξ₀ := by
    have h5 : z.re ≤ -R := by linarith
    have h4 : 4 * d.ξ₀ + Bz < 3 * R := by linarith
    linarith
  -- the balls of radii `‖z‖/4` and `‖z‖/10` around `z` stay in the sector
  have hball_gen : ∀ r : ℝ, r ≤ ‖z‖ / 4 → Metric.ball z r ⊆ MandelDim.QLeft d.ξ₀ := by
    intro r hr w hw
    have h1 : dist w z < r := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at h1
    have h2 : w.re - z.re ≤ ‖w - z‖ := by
      have h3 := Complex.abs_re_le_norm (w - z)
      rw [Complex.sub_re] at h3
      linarith [le_abs_self (w.re - z.re)]
    have h4 : w.re < -d.ξ₀ := by linarith [h1, h2, hr, hre_lt]
    exact Work.Parab.halfplane_subset_QLeft d.ξ₀ h4
  have hball4 : Metric.ball z (‖z‖ / 4) ⊆ MandelDim.QLeft d.ξ₀ := hball_gen _ le_rfl
  have hball10 : Metric.ball z (‖z‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ :=
    hball_gen _ (by linarith [norm_nonneg z])
  have hφz : d.φ z ≠ 0 :=
    hzero z hzQ (le_trans hR1R hznorm) hball4 z (Metric.mem_ball_self (by linarith))
  obtain ⟨hval, _hder⟩ := hXc z hzQ (by linarith) hball10
  -- the curve is bounded below: `‖Xc d z‖ ≥ ‖z‖/2`
  have hXclow : ‖z‖ / 2 ≤ ‖Work.Pert.Xc d z‖ := by
    have h1 : ‖z‖ ≤ ‖z - Work.Pert.Xc d z‖ + ‖Work.Pert.Xc d z‖ := by
      have h2 := norm_add_le (z - Work.Pert.Xc d z) (Work.Pert.Xc d z)
      rwa [sub_add_cancel] at h2
    have h3 : ‖z - Work.Pert.Xc d z‖ = ‖Work.Pert.Xc d z - z‖ := norm_sub_rev _ _
    have h4 : C₀ * (1 + Real.log ‖z‖) ≤ ‖z‖ / 2 := hRL ‖z‖ (le_trans hRLR hznorm)
    linarith
  -- hence `‖φ₀ z‖ ≤ 2/‖z‖`
  have hφbound : ‖d.φ z‖ ≤ 2 / ‖z‖ := by
    have hφnorm : ‖d.φ z‖ = 1 / ‖Work.Pert.Xc d z‖ := by
      have h : d.φ z = MandelDim.tau0 (Work.Pert.Xc d z) := by
        change d.φ z = MandelDim.tau0 (MandelDim.tau0 (d.φ z))
        rw [Work.Pert.tau0_tau0]
      rw [h, norm_tau0_le]
    rw [hφnorm]
    have h1 : (0 : ℝ) < ‖z‖ / 2 := by linarith
    calc 1 / ‖Work.Pert.Xc d z‖ ≤ 1 / (‖z‖ / 2) := one_div_le_one_div_of_le h1 hXclow
      _ = 2 / ‖z‖ := by ring
  -- and `‖deriv (Xc d) z‖ ≤ 1 + 2C₀`
  have hXcder : ‖deriv (Work.Pert.Xc d) z‖ ≤ 1 + 2 * C₀ := by
    have h1 : ‖deriv (Work.Pert.Xc d) z‖ ≤ 1 + C₀ * (1 + Real.log ‖z‖) / ‖z‖ := by
      have h2 := norm_add_le (deriv (Work.Pert.Xc d) z - 1) 1
      have h3 : deriv (Work.Pert.Xc d) z - 1 + 1 = deriv (Work.Pert.Xc d) z := by ring
      rw [h3, norm_one] at h2
      linarith
    have h4 : C₀ * (1 + Real.log ‖z‖) / ‖z‖ ≤ 2 * C₀ := by
      rw [div_le_iff₀ hzpos]
      have h5 : Real.log ‖z‖ ≤ ‖z‖ := by
        have h6 := Real.log_le_sub_one_of_pos hzpos
        linarith
      have h6 : C₀ ≤ C₀ * ‖z‖ := by nlinarith [hC₀, hznorm1]
      have h7 : C₀ * Real.log ‖z‖ ≤ C₀ * ‖z‖ := mul_le_mul_of_nonneg_left h5 hC₀.le
      linarith
    linarith
  -- chain rule: `deriv φ₀ = deriv (Xc d) · (φ₀)²`
  have hderiv_eq : deriv d.φ z = deriv (Work.Pert.Xc d) z * d.φ z ^ 2 := by
    have hdφ : DifferentiableAt ℂ d.φ z := d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hz)
    have hτ : DifferentiableAt ℂ MandelDim.tau0 (d.φ z) := by
      rw [show MandelDim.tau0 = fun y : ℂ => (-1 : ℂ) * y⁻¹ from rfl]
      exact (differentiableAt_inv_iff.mpr hφz).const_mul (-1)
    have hdt : deriv MandelDim.tau0 (d.φ z) = (d.φ z ^ 2)⁻¹ := by
      rw [show MandelDim.tau0 = fun y : ℂ => (-1 : ℂ) * y⁻¹ from rfl]
      rw [deriv_const_mul (-1) ((hasDerivAt_inv hφz).differentiableAt), deriv_inv]
      ring
    have hcomp : deriv (Work.Pert.Xc d) z = deriv MandelDim.tau0 (d.φ z) * deriv d.φ z := by
      change deriv (fun x => MandelDim.tau0 (d.φ x)) z =
        deriv MandelDim.tau0 (d.φ z) * deriv d.φ z
      exact deriv_comp (x := z) (h := d.φ) (h₂ := MandelDim.tau0) hτ hdφ
    rw [hcomp, hdt]
    field_simp
  rw [hderiv_eq, norm_mul, norm_pow]
  have hb2 : ‖d.φ z‖ ^ 2 ≤ (2 / ‖z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hφbound 2
  have hstep : ‖deriv (Work.Pert.Xc d) z‖ * ‖d.φ z‖ ^ 2 ≤ (1 + 2 * C₀) * (2 / ‖z‖) ^ 2 :=
    mul_le_mul hXcder hb2 (pow_nonneg (by positivity) 2) (by linarith)
  -- the sharp step: since `‖z‖ ≥ 1` the factor `(2/‖z‖)²` is at most `4`
  have hstep2 : (2 / ‖z‖) ^ 2 ≤ 4 := by
    have h2 : (2 / ‖z‖) ^ 2 = 4 / ‖z‖ ^ 2 := by ring
    rw [h2, div_le_iff₀ (pow_pos hzpos 2)]
    nlinarith [hznorm1]
  have hstep3 : (1 + 2 * C₀) * (2 / ‖z‖) ^ 2 ≤ (1 + 2 * C₀) * 4 :=
    mul_le_mul_of_nonneg_left hstep2 (by linarith)
  have hswap : (1 + 2 * C₀) * 4 = 4 * (1 + 2 * C₀) := by ring
  linarith

end Work.Pert.Ksub2
