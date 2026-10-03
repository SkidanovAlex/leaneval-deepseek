import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.phi_ne_zero_far
import Submission.Work.Parab.inversion.exists_mul_log_lt

/-!
# `Work.Pert.Ksub2.Xc_strip_nhd_bounds`

Uniform neighbourhood bounds for Shishikura's curve `Xc d u = τ₀ (φ₀ u)`
(`Work.Pert.Xc`) around the deep strip `Dstrip M T = {-M-1 ≤ Re u ≤ -M, |Im u| ≤ T}`.

For `M` large (depending on the datum `d` and on `T`, but not on `u`) and for every point
`z ∈ d.Dφ` at distance at most `1/4` from a point `u` of the strip:

* `‖deriv (Xc d) z‖ ≥ 1/2` — the curve is a local bi-Lipschitz chart in the deep region;
* `‖Xc d z‖ ≤ 3 M` — the curve does not leave the ball of radius `3M` (it is `≈ z`, and
  `‖z‖ ≤ 2M` there);
* `d.φ z ≠ 0` — the Fatou coordinate has no zero near the strip (its asymptotic value
  `z + a log(-z) + b` has modulus `≥ 1` there).

All three are harvested from two facts already proved in this workspace:

* `Xcurve_bounds` — the two-term asymptotic of `φ` together with Cauchy's estimate gives
  `‖Xc z - z‖ ≤ C (1 + log ‖z‖)` and `‖(Xc)' z - 1‖ ≤ C (1 + log ‖z‖)/‖z‖` on deep points
  `z` of the sector `QLeft ξ₀` whose `‖z‖/10`-ball stays in the sector;
* `exists_norm_add_clog_bound` — the quantitative `log = o(id)` fact making the right hand
  sides `≤ 1/2` resp. `≤ M/4` once `M` is large.

The geometric input is that a point at distance `≤ 1/4` from the strip has
`-M - 5/4 ≤ Re z ≤ -M + 1/4`, `|Im z| ≤ T + 1/4`, hence `M - 1/4 ≤ ‖z‖ ≤ M + T + 3/2`, so
both `z` and its `‖z‖/10`-ball lie in the left half-plane `{Re w < -ξ₀} ⊆ QLeft ξ₀`.
-/

namespace Work.Pert.Ksub2

open Complex Metric Filter

theorem Xc_strip_nhd_bounds {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (T : ℝ) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ u : ℂ, u ∈ Work.Pert.Dstrip M T →
      ∀ z : ℂ, z ∈ d.Dφ → ‖z - u‖ ≤ 1 / 4 →
      1 / 2 ≤ ‖deriv (Work.Pert.Xc d) z‖ ∧ ‖Work.Pert.Xc d z‖ ≤ 3 * M ∧ d.φ z ≠ 0 := by
  obtain ⟨C, hCpos, hXcur⟩ := Xcurve_bounds d
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨R_A, hR_A⟩ := hasym 1 one_pos
  obtain ⟨R_B, hR_B⟩ := Work.Pert.exists_norm_add_clog_bound a b 1 one_pos
  obtain ⟨R_L, -, hR_L⟩ :=
    Work.Parab.inversion.exists_mul_log_lt_aux (a := C) (b := C) (c := 1 / 4) (by norm_num)
  have hev : ∀ᶠ M : ℝ in Filter.atTop,
      1 ≤ M ∧ C + 2 ≤ M ∧ T + 3 ≤ M ∧ d.ξ₀ + 2 ≤ M ∧ max R_A R_B + 1 ≤ M ∧ R_L ≤ M ∧
        (10 / 9 : ℝ) * (d.ξ₀ + 1 / 4 + (T + 3 / 2) / 10 + 1) ≤ M := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), Filter.eventually_ge_atTop (C + 2),
      Filter.eventually_ge_atTop (T + 3), Filter.eventually_ge_atTop (d.ξ₀ + 2),
      Filter.eventually_ge_atTop (max R_A R_B + 1), Filter.eventually_ge_atTop R_L,
      Filter.eventually_ge_atTop ((10 / 9 : ℝ) * (d.ξ₀ + 1 / 4 + (T + 3 / 2) / 10 + 1))]
      with M h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max M₁ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro M hM u hu z hzD hzu
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) hM
  obtain ⟨hMge1, hMC, hMT, hMξ, hMRAB, hMRL, hMgeom⟩ := hM₁ M hM1
  -- ## geometry of the point `z` near the strip
  have hT0 : 0 ≤ T := le_trans (abs_nonneg u.im) hu.2.2
  have hdiff_re : |z.re - u.re| ≤ ‖z - u‖ := by
    have h := Complex.abs_re_le_norm (z - u)
    rwa [Complex.sub_re] at h
  have hdiff_im : |z.im - u.im| ≤ ‖z - u‖ := by
    have h := Complex.abs_im_le_norm (z - u)
    rwa [Complex.sub_im] at h
  have hre_ub : z.re ≤ -M + 1 / 4 := by
    have h := (abs_le.mp hdiff_re).2
    linarith [hu.2.1]
  have hre_lb : -M - 5 / 4 ≤ z.re := by
    have h := (abs_le.mp hdiff_re).1
    linarith [hu.1]
  have him_abs : |z.im| ≤ T + 1 / 4 := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h := (abs_le.mp hdiff_im).1
      have h2 := (abs_le.mp hu.2.2).1
      linarith
    · have h := (abs_le.mp hdiff_im).2
      have h2 := (abs_le.mp hu.2.2).2
      linarith
  have hzre_nonpos : z.re ≤ 0 := by linarith
  have hzn_ge : M - 1 / 4 ≤ ‖z‖ := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h2 : M - 1 / 4 ≤ |z.re| := by
      rw [abs_of_nonpos hzre_nonpos]
      linarith
    linarith
  have hzn_le : ‖z‖ ≤ M + T + 3 / 2 := by
    have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have h2 : |z.re| ≤ M + 5 / 4 := by
      rw [abs_of_nonpos hzre_nonpos]
      linarith
    linarith
  have hzn_le2 : ‖z‖ ≤ 2 * M := by linarith
  have hzn_pos : 0 < ‖z‖ := by linarith
  -- ## sector membership of `z` and of its `‖z‖/10`-ball
  have hzQ : z ∈ MandelDim.QLeft d.ξ₀ :=
    Work.Parab.halfplane_subset_QLeft d.ξ₀ (by linarith : z.re < -d.ξ₀)
  have hballQ : Metric.ball z (‖z‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ := by
    intro w hw
    refine Work.Parab.halfplane_subset_QLeft d.ξ₀ ?_
    show w.re < -d.ξ₀
    have h1 : dist w z < ‖z‖ / 10 := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at h1
    have h2 : w.re - z.re ≤ ‖w - z‖ := by
      have h := Complex.abs_re_le_norm (w - z)
      rw [Complex.sub_re] at h
      exact (abs_le.mp h).2
    have h3 : w.re < -M + 1 / 4 + ‖z‖ / 10 := by linarith
    have h4 : d.ξ₀ < M - 1 / 4 - ‖z‖ / 10 := by linarith
    linarith
  -- ## the two bounds of `Xcurve_bounds`
  have hC_le : C ≤ ‖z‖ := by linarith
  obtain ⟨hXval, hXder⟩ := hXcur z hzQ hC_le hballQ
  have hlog : Real.log ‖z‖ ≤ Real.log (2 * M) := Real.log_le_log hzn_pos hzn_le2
  have hClog : C * (1 + Real.log ‖z‖) ≤ C * (1 + Real.log (2 * M)) :=
    mul_le_mul_of_nonneg_left (by linarith) hCpos.le
  have hCval : C * (1 + Real.log ‖z‖) < M / 4 := by
    have hRL := hR_L M hMRL
    have heq : C * (1 + Real.log (2 * M)) = C * Real.log (2 * M) + C := by ring
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- derivative lower bound
    have hder_le : C * (1 + Real.log ‖z‖) / ‖z‖ ≤ 1 / 2 := by
      rw [div_le_iff₀ hzn_pos]
      have h2 : M / 4 ≤ (1 / 2) * ‖z‖ := by linarith
      linarith
    have hsum : (1 : ℝ) ≤ ‖deriv (Work.Pert.Xc d) z‖ + ‖deriv (Work.Pert.Xc d) z - 1‖ := by
      have h := norm_add_le (deriv (Work.Pert.Xc d) z) (1 - deriv (Work.Pert.Xc d) z)
      rw [show deriv (Work.Pert.Xc d) z + (1 - deriv (Work.Pert.Xc d) z) = (1 : ℂ) by ring,
        norm_one] at h
      rwa [norm_sub_rev (1 : ℂ) (deriv (Work.Pert.Xc d) z)] at h
    linarith
  · -- value bound
    have hXn : ‖Work.Pert.Xc d z‖ ≤ ‖Work.Pert.Xc d z - z‖ + ‖z‖ := by
      have h := norm_add_le (Work.Pert.Xc d z - z) z
      rwa [sub_add_cancel] at h
    linarith
  · -- nonvanishing of the Fatou coordinate
    intro hzero
    have hz0 : MandelDim.tau0 (d.φ z) = 0 := by rw [hzero]; simp [MandelDim.tau0]
    have hRA_le : R_A < ‖z‖ := by
      have h := le_max_left R_A R_B
      linarith
    have hRB_le : R_B ≤ ‖z‖ := by
      have h := le_max_right R_A R_B
      linarith
    have hasym_z : ‖MandelDim.tau0 (d.φ z) - (z + a * Complex.log (-z) + b)‖ < 1 :=
      hR_A z hzQ hRA_le
    have hcoer : (1 : ℝ) ≤ ‖z + a * Complex.log (-z) + b‖ := hR_B z hRB_le
    rw [hz0, zero_sub, norm_neg] at hasym_z
    linarith

end Work.Pert.Ksub2
