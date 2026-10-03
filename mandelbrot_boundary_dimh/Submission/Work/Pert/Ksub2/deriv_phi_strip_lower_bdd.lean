import Mathlib
import Submission.Work.Pert.Ksub2.deriv_phi_strip_lower
import Submission.Work.Pert.Ksub2.Xc_strip_nhd_bounds_bdd
import Submission.Work.Pert.Ksub2.Xc_strip_nhd_bounds
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.exists_norm_add_clog_bound
import Submission.Work.Parab.inversion.exists_mul_log_lt

/-!
# `Work.Pert.Ksub2.deriv_phi_strip_lower_bdd`

Explicit-threshold version of `Work.Pert.Ksub2.deriv_phi_strip_lower`: with the threshold

`E = max 1 (max (C+2) (max (T+3) (max (ξ₀+2) (max (max R_A R_B + 1)
      (max R_L ((10/9) * (ξ₀ + 1/4 + (T+3/2)/10 + 1))))))`

built from the constants of the asymptotic data, one has

`1 / 64 / (M * M) ≤ ‖deriv d.φ z‖`

for every `M ≥ E`, every `u ∈ Dstrip M T` and every `z ∈ d.Dφ` with `‖z - u‖ ≤ 1/4`.

The inputs are the explicit-threshold curvature bounds
`Work.Pert.Ksub2.Xc_strip_nhd_bounds_bdd` (`‖deriv (Xc d) z‖ ≥ 1/2`, `‖Xc d z‖ ≤ 3M`,
`φ₀ z ≠ 0`) together with the chain rule `deriv_phi_eq_deriv_Xc` of
`Work.Pert.Ksub2.deriv_phi_strip_lower`.
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Metric

theorem deriv_phi_strip_lower_bdd {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
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
        ‖z - u‖ ≤ 1 / 4 → 1 / 64 / (M * M) ≤ ‖deriv d.φ z‖ := by
  -- the explicit curvature bounds, at the same threshold `E`
  obtain ⟨M₁, _hM₁pos, hM₁le, hM₁bnd⟩ := Xc_strip_nhd_bounds_bdd d hC hXcur hA hB hL
  set E : ℝ := max 1 (max (C + 2) (max (T + 3) (max (d.ξ₀ + 2)
      (max (max R_A R_B + 1) (max R_L ((10 / 9) * (d.ξ₀ + 1 / 4 + (T + 3 / 2) / 10 + 1)))))))
    with hE
  refine ⟨E, lt_of_lt_of_le one_pos (le_max_left _ _), le_refl E, ?_⟩
  intro M hM u hu z hzD hzu
  have hM1 : (1 : ℝ) ≤ M := le_trans (le_max_left _ _) hM
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  obtain ⟨hder, hval, hne⟩ := hM₁bnd M (le_trans hM₁le hM) u hu z hzD hzu
  -- `‖Xc d z‖ = 1 / ‖d.φ z‖`
  have hXcnorm : ‖Work.Pert.Xc d z‖ = 1 / ‖d.φ z‖ := by
    rw [show Work.Pert.Xc d = fun y : ℂ => MandelDim.tau0 (d.φ y) from rfl]
    show ‖MandelDim.tau0 (d.φ z)‖ = 1 / ‖d.φ z‖
    rw [show MandelDim.tau0 (d.φ z) = (-1 : ℂ) / d.φ z from rfl, norm_div, norm_neg, norm_one]
  have hφnz : ‖d.φ z‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hφlow : 1 / (3 * M) ≤ ‖d.φ z‖ := by
    have h3M : (0 : ℝ) < 3 * M := by linarith
    have hle : 1 / ‖d.φ z‖ ≤ 3 * M := by rw [← hXcnorm]; exact hval
    rw [div_le_iff₀ h3M]
    have hmul := mul_le_mul_of_nonneg_left hle (norm_nonneg (d.φ z))
    rw [mul_one_div, div_self hφnz] at hmul
    linarith
  -- assemble: `‖φ₀' z‖ = ‖(Xc d)' z‖ · ‖φ₀ z‖²`
  have hsq : (1 / (3 * M)) ^ 2 ≤ ‖d.φ z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hφlow 2
  have hmain : (1 / 2) * (1 / (3 * M)) ^ 2
      ≤ ‖deriv (Work.Pert.Xc d) z‖ * ‖d.φ z‖ ^ 2 :=
    mul_le_mul hder hsq (by positivity) (by positivity)
  rw [deriv_phi_eq_deriv_Xc d hzD hne, norm_mul, norm_pow]
  refine le_trans ?_ hmain
  have hMM : (0 : ℝ) < M * M := mul_pos hMpos hMpos
  rw [div_le_iff₀ hMM]
  have hM0 : M ≠ 0 := ne_of_gt hMpos
  field_simp
  ring_nf
  norm_num

end Work.Pert.Ksub2
