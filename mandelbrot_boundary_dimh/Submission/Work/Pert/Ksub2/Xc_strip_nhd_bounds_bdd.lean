import Mathlib
import Submission.Work.Pert.Ksub2.Xc_strip_nhd_bounds
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.exists_norm_add_clog_bound
import Submission.Work.Parab.inversion.exists_mul_log_lt

/-!
# `Work.Pert.Ksub2.Xc_strip_nhd_bounds_bdd`

Same content as `Work.Pert.Ksub2.Xc_strip_nhd_bounds`, but with an *explicit* bound on the
threshold `M₀`: for the datum's curve `Xc d u = τ₀ (φ₀ u)`, for every point `z ∈ d.Dφ` at distance
at most `1/4` from the deep strip `Dstrip M T = {-M-1 ≤ Re u ≤ -M, |Im u| ≤ T}`,

* `‖deriv (Xc d) z‖ ≥ 1/2`,
* `‖Xc d z‖ ≤ 3 M`,
* `d.φ z ≠ 0`,

for all `M ≥ M₀`, where

`M₀ = max 1 (max (C+2) (max (T+3) (max (ξ₀+2) (max (max R_A R_B + 1)
        (max R_L ((10/9) * (ξ₀ + 1/4 + (T+3/2)/10 + 1)))))))`

is built from the constants of the asymptotic data (`C` from the two-term asymptotic, `R_A`, `R_B`
for the *modulus* bounds furnished by `hA` and `hB`, and `R_L` for the logarithmic comparison
`hL`).  The argument is the one of `Xc_strip_nhd_bounds`, read with the explicit threshold in place
of the `∀ᶠ M` produced by `eventually_atTop`.
-/

namespace Work.Pert.Ksub2

open Complex Metric Filter

theorem Xc_strip_nhd_bounds_bdd {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {T C R_A R_B R_L : ℝ} {a b : ℂ}
    (hC : 0 < C)
    (hXcur : ∀ u : ℂ, u ∈ MandelDim.QLeft d.ξ₀ → C ≤ ‖u‖ →
      Metric.ball u (‖u‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ →
      ‖Work.Pert.Xc d u - u‖ ≤ C * (1 + Real.log ‖u‖) ∧
      ‖deriv (Work.Pert.Xc d) u - 1‖ ≤ C * (1 + Real.log ‖u‖) / ‖u‖)
    (hA : ∀ w : ℂ, w ∈ MandelDim.QLeft d.ξ₀ → R_A < ‖w‖ →
      ‖MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b)‖ < 1)
    (hB : ∀ u : ℂ, R_B ≤ ‖u‖ → 1 ≤ ‖u + a * Complex.log (-u) + b‖)
    (hL : ∀ x : ℝ, R_L ≤ x → C * Real.log (2 * x) + C < x / 4) :
    ∃ M₀ : ℝ, 0 < M₀ ∧
      M₀ ≤ max 1 (max (C + 2) (max (T + 3) (max (d.ξ₀ + 2)
        (max (max R_A R_B + 1) (max R_L ((10 / 9) * (d.ξ₀ + 1 / 4 + (T + 3 / 2) / 10 + 1))))))) ∧
      ∀ M : ℝ, M₀ ≤ M → ∀ u : ℂ, u ∈ Work.Pert.Dstrip M T → ∀ z : ℂ, z ∈ d.Dφ →
        ‖z - u‖ ≤ 1 / 4 →
        1 / 2 ≤ ‖deriv (Work.Pert.Xc d) z‖ ∧ ‖Work.Pert.Xc d z‖ ≤ 3 * M ∧ d.φ z ≠ 0 := by
  set G : ℝ := (10 / 9) * (d.ξ₀ + 1 / 4 + (T + 3 / 2) / 10 + 1) with hG
  set E : ℝ := max 1 (max (C + 2) (max (T + 3) (max (d.ξ₀ + 2)
      (max (max R_A R_B + 1) (max R_L G))))) with hE
  -- ## the components of `E` are below `E`
  have hE1 : (1 : ℝ) ≤ E := by rw [hE]; exact le_max_left _ _
  have hEC : C + 2 ≤ E := by
    rw [hE]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hET : T + 3 ≤ E := by
    rw [hE]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hEξ : d.ξ₀ + 2 ≤ E := by
    rw [hE]
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)
  have hERAB : max R_A R_B + 1 ≤ E := by
    rw [hE]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hERL : R_L ≤ E := by
    rw [hE]
    refine le_trans (le_max_left R_L G) ?_
    refine le_trans (le_max_right (max R_A R_B + 1) _) ?_
    refine le_trans (le_max_right (d.ξ₀ + 2) _) ?_
    refine le_trans (le_max_right (T + 3) _) ?_
    exact le_trans (le_max_right (C + 2) _) (le_max_right 1 _)
  have hEG : G ≤ E := by
    rw [hE]
    refine le_trans (le_max_right R_L G) ?_
    refine le_trans (le_max_right (max R_A R_B + 1) _) ?_
    refine le_trans (le_max_right (d.ξ₀ + 2) _) ?_
    refine le_trans (le_max_right (T + 3) _) ?_
    exact le_trans (le_max_right (C + 2) _) (le_max_right 1 _)
  refine ⟨E, lt_of_lt_of_le one_pos hE1, le_refl E, ?_⟩
  intro M hM u hu z hzD hzu
  have hM1 : 1 ≤ M := le_trans hE1 hM
  have hMC : C + 2 ≤ M := le_trans hEC hM
  have hMT : T + 3 ≤ M := le_trans hET hM
  have hMξ : d.ξ₀ + 2 ≤ M := le_trans hEξ hM
  have hMRAB : max R_A R_B + 1 ≤ M := le_trans hERAB hM
  have hMRL : R_L ≤ M := le_trans hERL hM
  have hMgeom : G ≤ M := le_trans hEG hM
  rw [hG] at hMgeom
  -- ## geometry of the point `z` near the strip
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
  -- ## the two bounds of `hXcur`
  have hC_le : C ≤ ‖z‖ := by linarith
  obtain ⟨hXval, hXder⟩ := hXcur z hzQ hC_le hballQ
  have hlog : Real.log ‖z‖ ≤ Real.log (2 * M) := Real.log_le_log hzn_pos hzn_le2
  have hClog : C * (1 + Real.log ‖z‖) ≤ C * (1 + Real.log (2 * M)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC.le
  have hCval : C * (1 + Real.log ‖z‖) < M / 4 := by
    have hRL := hL M hMRL
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
      hA z hzQ hRA_le
    have hcoer : (1 : ℝ) ≤ ‖z + a * Complex.log (-z) + b‖ := hB z hRB_le
    rw [hz0, zero_sub, norm_neg] at hasym_z
    linarith

end Work.Pert.Ksub2
