import Mathlib
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.phi_ne_zero_far
import Submission.Work.Parab.Setup

/-!
# `Work.Pert.Ksub2.deriv_phi_deep_upper`

A **uniform upper bound for `‖deriv φ₀‖` on the deep part of Shishikura's repelling sector**.

The datum's coordinate `φ₀` is a change of variable `z ↦ -1/z` away from the limit map: with
`Xc d u = τ₀ (φ₀ u)` (the curve of `Xcurve_bounds`, which is asymptotically the identity, with a
`log`-error), one has `φ₀ u = τ₀ (Xc d u)`.  The chain rule gives

  `deriv φ₀ u = deriv (Xc d) u · (φ₀ u)²`,

and both factors are *small* on the deep region `{Re u ≪ 0, |Im u| ≤ Bz}`:

* `‖deriv (Xc d) u‖ ≤ 1 + C₀ (1 + log ‖u‖)/‖u‖ ≤ 1 + 2C₀` (`Xcurve_bounds`), and
* `‖φ₀ u‖ = 1/‖Xc d u‖ ≤ 2/‖u‖`, because `‖Xc d u - u‖ ≤ C₀ (1 + log ‖u‖) ≤ ‖u‖/2` there.

So `∃ R C > 0`, `∀ z ∈ Dφ`, `-z.re ≥ R ⇒ |z.im| ≤ Bz ⇒ ‖deriv φ₀ z‖ ≤ C` — this is the
`deriv_phi_deep_upper` form of the datum's derivative bound used by the perturbation argument
(`deriv_phi_bounds_walk`, `Ksub_phi_close_v2`).

The geometry is elementary: a point with `Re z ≤ -R` (`R` large relative to `ξ₀` and the imaging
bound `Bz`) lies in the half-plane `{Re w < -ξ₀} ⊆ QLeft ξ₀`, and so does the ball of radius
`‖z‖/4` around it, since `‖z‖ ≤ |Re z| + |Im z| ≤ -Re z + Bz` grows at most linearly in `-Re z`.
The only "hard" input is the elementary `log = o(id)` estimate, proved here as
`eventually_mul_log_le_half` from `Real.isLittleO_log_id_atTop`.
-/

namespace Work.Pert.Ksub2

open Complex Metric

/-- `‖τ₀ w‖ = 1/‖w‖` (`τ₀ w = -1/w`). -/
private lemma norm_tau0' (w : ℂ) : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by
  simp [MandelDim.tau0, norm_neg, norm_one]

/-- The elementary `log = o(id)` estimate, in the form needed for the depth threshold:
for every `C > 0` there is `R` with `C * (1 + log x) ≤ x/2` for all `x ≥ R`. -/
private lemma eventually_mul_log_le_half (C : ℝ) (hC : 0 < C) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ x → C * (1 + Real.log x) ≤ x / 2 := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ (1 / (4 * C)) * x := by
    have hlo : (fun x : ℝ => Real.log x) =o[Filter.atTop] (fun x : ℝ => x) :=
      Real.isLittleO_log_id_atTop
    filter_upwards [Asymptotics.isLittleO_iff.mp hlo (by positivity : (0:ℝ) < 1/(4*C)),
      Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (by linarith)] at hx
    exact hx
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp (h1.and (Filter.eventually_ge_atTop (4 * C)))
  refine ⟨max R₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => ?_⟩
  have hxR : R₀ ≤ x := le_trans (le_max_left _ _) hx
  obtain ⟨ha, hb⟩ := hR₀ x hxR
  have hC4 : C * (1 / (4 * C)) = 1 / 4 := by field_simp
  have h2 : C * Real.log x ≤ x / 4 := by
    calc C * Real.log x ≤ C * ((1 / (4 * C)) * x) := mul_le_mul_of_nonneg_left ha hC.le
      _ = x / 4 := by rw [← mul_assoc, hC4]; ring
  have h3 : C ≤ x / 4 := by linarith
  linarith

theorem deriv_phi_deep_upper {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (Bz : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ℂ, z ∈ d.Dφ → R ≤ -z.re → |z.im| ≤ Bz →
      ‖deriv d.φ z‖ ≤ C := by
  obtain ⟨C₀, hC₀pos, hXc⟩ := Work.Pert.Ksub2.Xcurve_bounds d
  obtain ⟨R₁, _hR₁pos, hR₁⟩ := Work.Pert.phi_ne_zero_far d
  obtain ⟨RL, _hRLpos, hRL⟩ := eventually_mul_log_le_half C₀ hC₀pos
  -- replace the imaging bound by a nonnegative one (the hypothesis is unsatisfiable otherwise)
  set Bz' : ℝ := max Bz 0 with hBz'def
  have hBz'le : Bz ≤ Bz' := by rw [hBz'def]; exact le_max_left _ _
  -- the depth threshold: large relative to the datum, the log threshold and `Bz`
  have hev : ∀ᶠ R : ℝ in Filter.atTop,
      d.ξ₀ + 1 ≤ R ∧ C₀ + 1 ≤ R ∧ RL ≤ R ∧ R₁ ≤ R ∧ 1 ≤ R ∧
        (4 * d.ξ₀ + Bz') / 3 + 1 ≤ R := by
    filter_upwards [Filter.eventually_ge_atTop (d.ξ₀ + 1), Filter.eventually_ge_atTop (C₀ + 1),
      Filter.eventually_ge_atTop RL, Filter.eventually_ge_atTop R₁,
      Filter.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_ge_atTop ((4 * d.ξ₀ + Bz') / 3 + 1)] with R h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨hRξ, hRC, hRLR, hR1R, hR1', hRbig⟩ := hR R le_rfl
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1'
  refine ⟨R, (1 + 2 * C₀) * (4 / R ^ 2), hRpos,
    mul_pos (by linarith) (div_pos (by norm_num) (pow_pos hRpos 2)), ?_⟩
  intro z hz hzre hzim
  -- `z` is deep and to the left
  have hznorm : R ≤ ‖z‖ := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h2 : |z.re| = -z.re := abs_of_nonpos (by linarith)
    linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hRpos hznorm
  have hznorm1 : (1 : ℝ) ≤ ‖z‖ := le_trans hR1' hznorm
  have hnormle : ‖z‖ ≤ -z.re + Bz' := by
    have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have h2 : |z.re| = -z.re := abs_of_nonpos (by linarith)
    have h3 : |z.im| ≤ Bz' := le_trans hzim hBz'le
    linarith
  have hzlt : z.re < -d.ξ₀ := by linarith [hRξ, hzre]
  have hzQ : z ∈ MandelDim.QLeft d.ξ₀ := Work.Parab.halfplane_subset_QLeft d.ξ₀ hzlt
  have hre_lt : z.re + ‖z‖ / 4 < -d.ξ₀ := by
    have h5 : z.re ≤ -R := by linarith
    have h4 : 4 * d.ξ₀ + Bz' < 3 * R := by linarith
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
    hR₁ z hzQ (le_trans hR1R hznorm) hball4 z (Metric.mem_ball_self (by linarith))
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
      rw [h, norm_tau0']
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
      have h6 : C₀ ≤ C₀ * ‖z‖ := by nlinarith [hC₀pos, hznorm1]
      have h7 : C₀ * Real.log ‖z‖ ≤ C₀ * ‖z‖ := mul_le_mul_of_nonneg_left h5 hC₀pos.le
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
  have hstep2 : (2 / ‖z‖) ^ 2 ≤ 4 / R ^ 2 := by
    have h2 : (2 / ‖z‖) ^ 2 = 4 / ‖z‖ ^ 2 := by ring
    have h3 : (4 : ℝ) / ‖z‖ ^ 2 ≤ 4 / R ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos hRpos 2)
        (pow_le_pow_left₀ hRpos.le hznorm 2)
    rw [h2]; exact h3
  have hstep3 : (1 + 2 * C₀) * (2 / ‖z‖) ^ 2 ≤ (1 + 2 * C₀) * (4 / R ^ 2) :=
    mul_le_mul_of_nonneg_left hstep2 (by linarith)
  linarith

end Work.Pert.Ksub2
