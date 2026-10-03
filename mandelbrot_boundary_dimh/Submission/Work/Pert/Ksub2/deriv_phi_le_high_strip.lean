import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.Ksub2.F0f_far_translation
import Submission.Work.Pert.Ksub2.deriv_phi_deep_upper_bdd
import Submission.Work.Pert.Ksub2.deriv_phi_strip_lower
import Submission.Work.Pert.Ksub2.tau0_phi_band_norm_le_nh
import Submission.Work.Pert.Ksub2.phi_norm_le_of_far_re_le_one
import Submission.Work.Pert.Ksub2.phi_norm_le_of_far_re_le
import Submission.Work.Parab.Setup

/-!
# `Work.Pert.Ksub2.deriv_phi_le_high_strip`

`‖deriv φ₀‖` is bounded on the *high strip* `{|Im z| ≥ y, Re z ≤ B}` of a §4.1-datum, for every
`y > η₀` and every real `B`.

The proof splits that unbounded region at `‖z‖ = R`:

* **near part** (`‖z‖ ≤ R`): the set `{y ≤ |Im z|, Re z ≤ B, ‖z‖ ≤ R}` is compact and contained
  in the open maximal domain `Dφ` (every point of it has `|Im| ≥ y > η₀`, so `ParabData.ends_sub`
  applies), hence `deriv φ₀` is bounded on it (`IsCompact.exists_bound_of_continuousOn`, using
  that `deriv φ₀` is holomorphic on `Dφ` by `DifferentiableOn.deriv`).
* **far part** (`‖z‖ ≥ R`): there `φ₀` is *small* on the whole ball of radius
  `r = (y - η₀)/2` around `z` — every point `u` of that closed ball has `|Im u| ≥ y - r > η₀`
  (so `u ∈ Dφ`) and `Re u ≤ B + r`, and for those the half-plane smallness of the coordinate
  `Work.Pert.Ksub2.phi_norm_le_of_far_re_le` (a strengthening of
  `Work.Pert.Ksub2.phi_norm_le_of_far_re_le_one` to an arbitrary right boundary `B`) gives
  `‖φ₀ u‖ ≤ ε · r`.  Cauchy's estimate
  (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) on that ball then yields
  `‖deriv φ₀ z‖ ≤ (ε r)/r = ε`.

The constant `Cd` is the maximum of the two bounds.
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Metric

/-- **`deriv φ₀` is uniformly small far out in the high strip.**  For every `y > η₀`, every real
`B` and every `ε > 0` there is `R` such that `‖deriv φ₀ z‖ ≤ ε` at every `z` with
`y ≤ |Im z|`, `Re z ≤ B` and `R ≤ ‖z‖`.

Take `r = (y - η₀)/2`.  On the closed ball `B(z,r)` every point has `|Im| ≥ y - r > η₀` (so the
ball lies in `Dφ`) and `Re ≤ B + r`, and its norm is `≥ ‖z‖ - r`; the half-plane smallness
`phi_norm_le_of_far_re_le` (with half-plane bound `B + r` and constant `ε r`) therefore gives
`‖φ₀‖ ≤ ε r` on the ball, and Cauchy's estimate turns that into `‖deriv φ₀ z‖ ≤ ε`. -/
private theorem deriv_phi_small_far {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {y B ε : ℝ} (hy : d.η₀ < y) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      ∀ z : ℂ, y ≤ |z.im| → z.re ≤ B → R ≤ ‖z‖ → ‖deriv d.φ z‖ ≤ ε := by
  set r : ℝ := (y - d.η₀) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hεr : 0 < ε * r := mul_pos hε hrpos
  obtain ⟨Rs, hRspos, hfar⟩ :=
    phi_norm_le_of_far_re_le d (c := ε * r) (B := B + r) hεr
  refine ⟨Rs + r + 1, by linarith, ?_⟩
  intro z hzim hzre hzR
  -- the closed `r`-ball around `z` lies in the maximal domain
  have hballD : Metric.closedBall z r ⊆ d.Dφ := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    have h2 : |u.im - z.im| ≤ r := by
      have h := Complex.abs_im_le_norm (u - z)
      rw [Complex.sub_im] at h
      linarith
    have h3 : |z.im| - |u.im| ≤ r := by
      have h := abs_sub_abs_le_abs_sub z.im u.im
      rw [abs_sub_comm] at h
      linarith
    have him : y - r ≤ |u.im| := by linarith
    have hlt : d.η₀ < |u.im| := by
      have : d.η₀ < y - r := by rw [hr]; linarith
      linarith
    exact (d.ends_sub u hlt).1
  -- `φ₀` is small on the sphere
  have hsphere : ∀ u ∈ Metric.sphere z r, ‖d.φ u‖ ≤ ε * r := by
    intro u hu
    rw [Metric.mem_sphere, dist_eq_norm] at hu
    have h1 : u.re ≤ B + r := by
      have h2 : |u.re - z.re| ≤ r := by
        have h := Complex.abs_re_le_norm (u - z)
        rw [Complex.sub_re] at h
        linarith
      have h3 : u.re - z.re ≤ |u.re - z.re| := le_abs_self _
      linarith
    have h4 : Rs ≤ ‖u‖ := by
      have h5 : ‖z‖ ≤ ‖z - u‖ + ‖u‖ := by
        calc ‖z‖ = ‖(z - u) + u‖ := by ring_nf
          _ ≤ ‖z - u‖ + ‖u‖ := norm_add_le _ _
      have h6 : ‖z - u‖ = r := by rw [norm_sub_rev, hu]
      linarith
    exact hfar u h1 h4
  -- Cauchy's estimate on the ball
  have hdiff : DiffContOnCl ℂ d.φ (Metric.ball z r) :=
    (d.φ_holo.mono (by rw [closure_ball z (ne_of_gt hrpos)]; exact hballD)).diffContOnCl
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := d.φ) (c := z)
    (R := r) (C := ε * r) hrpos hdiff hsphere
  calc ‖deriv d.φ z‖ ≤ (ε * r) / r := hcau
    _ = ε := by rw [mul_div_assoc, div_self (ne_of_gt hrpos), mul_one]

theorem deriv_phi_le_high_strip {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {y B : ℝ} (hy : d.η₀ < y) :
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ z : ℂ, z ∈ d.Dφ → y ≤ |z.im| → z.re ≤ B → ‖deriv d.φ z‖ ≤ Cd := by
  obtain ⟨R, _hRpos, hfar⟩ := deriv_phi_small_far d hy (ε := 1) one_pos
  -- the compact near part `{y ≤ |Im|, Re ≤ B, ‖·‖ ≤ R}` lies in the open domain `d.Dφ`
  have hKc : IsCompact {z : ℂ | y ≤ |z.im| ∧ z.re ≤ B ∧ ‖z‖ ≤ R} := by
    have hclosed : IsClosed {z : ℂ | y ≤ |z.im| ∧ z.re ≤ B ∧ ‖z‖ ≤ R} :=
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im)).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          (isClosed_le continuous_norm continuous_const))
    refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hclosed ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hz.2.2
  have hKsub : {z : ℂ | y ≤ |z.im| ∧ z.re ≤ B ∧ ‖z‖ ≤ R} ⊆ d.Dφ := fun z hz =>
    (d.ends_sub z (lt_of_lt_of_le hy hz.1)).1
  have hcont : ContinuousOn (deriv d.φ) {z : ℂ | y ≤ |z.im| ∧ z.re ≤ B ∧ ‖z‖ ≤ R} :=
    ((d.φ_holo.deriv d.Dφ_open).continuousOn).mono hKsub
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max M 1, lt_max_of_lt_right one_pos, ?_⟩
  intro z _hzD hzim hzre
  rcases le_or_gt ‖z‖ R with hle | hlt
  · exact le_trans (hM z ⟨hzim, hzre, hle⟩) (le_max_left _ _)
  · exact le_trans (hfar z hzim hzre (le_of_lt hlt)) (le_max_right _ _)

end Work.Pert.Ksub2
