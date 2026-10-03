import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.inversion.neg_mem_slitPlane_of_mem_QLeft
import Submission.Work.Pert.exists_norm_add_clog_bound

/-!
# `Work.Pert.deriv_psi0_close`

Shishikura's Appendix A.4, the analytic core of the perturbed-coordinate estimate.

`ParabData.φ_asymp` gives the Cayley-coordinate asymptotic
`tau0 (φ w) = w + a log(-w) + b + o(1)` on Shishikura's sector `QLeft ξ₀`.
Differentiating it at a point `w` whose whole disc `ball w (‖w‖/10)` still lies in the
sector (a hypothesis of the statement, and exactly the situation in which the field is
used), the derivative of the error term is bounded by Cauchy's estimate, whence
`deriv (tau0 ∘ φ) w → 1` as `‖w‖ → ∞`.

We use the workspace lemma `Work.Parab.inversion.neg_mem_slitPlane_of_mem_QLeft` which
shows that the principal branch of `log (-·)` is holomorphic on such a disc, and the
auxiliary coercivity estimate `Work.Pert.exists_norm_add_clog_bound` (`‖u + a log(-u) + b‖`
is eventually large, hence `φ u ≠ 0` there, so `tau0 ∘ φ` is holomorphic too).
-/

namespace Work.Pert

open Complex

private lemma differentiableAt_tau0 {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ MandelDim.tau0 z :=
  (differentiableAt_const (-1)).div differentiableAt_id (by simpa using hz)

theorem deriv_psi0_close {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, w ∈ MandelDim.QLeft d.ξ₀ → R ≤ ‖w‖ →
      Metric.ball w (‖w‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ →
      ‖deriv (fun u : ℂ => MandelDim.tau0 (d.φ u)) w - 1‖ ≤ 1 / 2 := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  have hξ : 0 < d.ξ₀ := d.ξ₀_pos
  have hε : 0 < (1 / 100 : ℝ) := by norm_num
  obtain ⟨R₁, hR₁⟩ := hasym (1 / 100) hε
  obtain ⟨R₂, hR₂⟩ := exists_norm_add_clog_bound a b (1 / 100) hε
  set R : ℝ := max (max (2 * R₁ + 2) (2 * R₂ + 2))
      (max (max (d.ξ₀ + 1) 20) (40 * (1 / 100) + 2 * ‖a‖ + 1)) with hRdef
  have hR_ge20 : (20 : ℝ) ≤ R := by
    rw [hRdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hR1 : 2 * R₁ + 2 ≤ R := by
    rw [hRdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hR2 : 2 * R₂ + 2 ≤ R := by
    rw [hRdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hRxi : d.ξ₀ + 1 ≤ R := by
    rw [hRdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hRA : 40 * (1 / 100 : ℝ) + 2 * ‖a‖ + 1 ≤ R := by
    rw [hRdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨R, lt_of_lt_of_le (by norm_num) hR_ge20, ?_⟩
  intro w hwQ hwR hball
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) (le_trans hR_ge20 hwR)
  have hxi_lt : d.ξ₀ < ‖w‖ := by have := le_trans hRxi hwR; linarith
  have hR1w : R₁ < 9 * ‖w‖ / 10 := by have := le_trans hR1 hwR; linarith
  have hR2w : R₂ ≤ 9 * ‖w‖ / 10 := by have := le_trans hR2 hwR; linarith
  -- every point of the big disc is far out (so `φ = 0` is impossible there) and
  -- stays off the branch cut of `log (-·)`
  have hlb : ∀ u ∈ Metric.ball w (‖w‖ / 10), 9 * ‖w‖ / 10 ≤ ‖u‖ := by
    intro u hu
    have h1 : dist u w < ‖w‖ / 10 := Metric.mem_ball.mp hu
    have h2 : ‖u - w‖ < ‖w‖ / 10 := by rwa [dist_eq_norm] at h1
    have h3 : ‖w‖ ≤ ‖w - u‖ + ‖u‖ := by
      have h := norm_add_le (w - u) u
      rwa [sub_add_cancel] at h
    have h4 : ‖w - u‖ = ‖u - w‖ := norm_sub_rev w u
    linarith
  have hslit : ∀ u ∈ Metric.ball w (‖w‖ / 10), -u ∈ Complex.slitPlane := by
    intro u hu
    have h1 : ‖u - w‖ < ‖w‖ / 10 := by
      have h := Metric.mem_ball.mp hu
      rwa [dist_eq_norm] at h
    have h2 : (‖w‖ : ℝ) / 10 < ‖w‖ / 8 := by linarith
    exact Work.Parab.inversion.neg_mem_slitPlane_of_mem_QLeft (w := w) (x := u) hξ hwQ hxi_lt
      (le_of_lt (lt_trans h1 h2))
  have hzu : ∀ u ∈ Metric.ball w (‖w‖ / 10), d.φ u ≠ 0 := by
    intro u hu hzero
    have hge := hlb u hu
    have herr := hR₁ u (hball hu) (lt_of_lt_of_le hR1w hge)
    have hlow := hR₂ u (le_trans hR2w hge)
    have hz : MandelDim.tau0 (d.φ u) = 0 := by rw [hzero]; simp [MandelDim.tau0]
    rw [hz, zero_sub, norm_neg] at herr
    linarith
  set L : ℂ → ℂ := fun u => u + a * Complex.log (-u) + b with hLdef
  set G : ℂ → ℂ := fun u => MandelDim.tau0 (d.φ u) - L u with hGdef
  have hTau : ∀ u ∈ Metric.ball w (‖w‖ / 10),
      DifferentiableAt ℂ (fun u : ℂ => MandelDim.tau0 (d.φ u)) u := by
    intro u hu
    have hphi : DifferentiableAt ℂ d.φ u :=
      d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds (d.Q_sub (hball hu)))
    exact (differentiableAt_tau0 (hzu u hu)).comp u hphi
  have hLat : ∀ u ∈ Metric.ball w (‖w‖ / 10), DifferentiableAt ℂ L u := by
    intro u hu
    have hlog : DifferentiableAt ℂ (fun u : ℂ => Complex.log (-u)) u :=
      differentiableAt_id.neg.clog (hslit u hu)
    have h1 : DifferentiableAt ℂ (fun u : ℂ => a * Complex.log (-u)) u :=
      hlog.const_mul a
    have h2 : DifferentiableAt ℂ (fun u : ℂ => u + a * Complex.log (-u) + b) u :=
      (differentiableAt_id.add h1).add_const b
    simpa [hLdef] using h2
  have hGdiff : DifferentiableOn ℂ G (Metric.ball w (‖w‖ / 10)) := by
    intro u hu
    have h3 : DifferentiableAt ℂ (fun u : ℂ => MandelDim.tau0 (d.φ u) - L u) u :=
      (hTau u hu).sub (hLat u hu)
    simpa [hGdef] using h3.differentiableWithinAt
  have hr_pos : 0 < ‖w‖ / 20 := by linarith
  have hGcont : ContinuousOn G (Metric.closedBall w (‖w‖ / 20)) :=
    hGdiff.continuousOn.mono (Metric.closedBall_subset_ball (by linarith))
  have hdiffSmall : DifferentiableOn ℂ G (Metric.ball w (‖w‖ / 20)) :=
    hGdiff.mono (Metric.ball_subset_ball (by linarith))
  have hdc : DiffContOnCl ℂ G (Metric.ball w (‖w‖ / 20)) := by
    refine ⟨hdiffSmall, ?_⟩
    rw [closure_ball w (ne_of_gt hr_pos)]
    exact hGcont
  have hCauchy : ‖deriv G w‖ ≤ (1 / 100) / (‖w‖ / 20) := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr_pos hdc
    intro z hz
    have hzdist : dist z w = ‖w‖ / 20 := Metric.mem_sphere.mp hz
    have hzbig : z ∈ Metric.ball w (‖w‖ / 10) := by
      rw [Metric.mem_ball]; rw [hzdist]; linarith
    have hge := hlb z hzbig
    have herr := hR₁ z (hball hzbig) (lt_of_lt_of_le hR1w hge)
    have : ‖G z‖ < 1 / 100 := by simpa [hGdef, hLdef] using herr
    exact le_of_lt this
  have hwmem : w ∈ Metric.ball w (‖w‖ / 10) := by
    rw [Metric.mem_ball, dist_self]; linarith
  have hGw : DifferentiableAt ℂ G w := by
    have h3 : DifferentiableAt ℂ (fun u : ℂ => MandelDim.tau0 (d.φ u) - L u) w :=
      (hTau w hwmem).sub (hLat w hwmem)
    simpa [hGdef] using h3
  have hLderiv : deriv L w = 1 + a / w := by
    have hlog : HasDerivAt (fun u : ℂ => Complex.log (-u)) ((-1) / (-w)) w :=
      (hasDerivAt_id w).neg.clog (hslit w hwmem)
    have hL : HasDerivAt L (1 + a * ((-1) / (-w))) w := by
      have h := (((hasDerivAt_id w).add (hlog.const_mul a)).add_const b)
      simpa [hLdef] using h
    rw [hL.deriv]
    have h2 : (-1 : ℂ) / (-w) = 1 / w := by
      rw [div_eq_mul_inv, div_eq_mul_inv, inv_neg]; ring
    rw [h2]; ring
  have hderivH : deriv (fun u : ℂ => MandelDim.tau0 (d.φ u)) w = deriv G w + deriv L w := by
    have h1 : (fun u : ℂ => MandelDim.tau0 (d.φ u)) = fun u => G u + L u := by
      funext u; simp [hGdef, hLdef]
    rw [h1]
    exact deriv_add hGw (hLat w hwmem)
  calc ‖deriv (fun u : ℂ => MandelDim.tau0 (d.φ u)) w - 1‖
      = ‖deriv G w + deriv L w - 1‖ := by rw [hderivH]
    _ = ‖deriv G w + a / w‖ := by rw [hLderiv]; ring_nf
    _ ≤ ‖deriv G w‖ + ‖a / w‖ := norm_add_le _ _
    _ = ‖deriv G w‖ + ‖a‖ / ‖w‖ := by rw [norm_div]
    _ ≤ (1 / 100) / (‖w‖ / 20) + ‖a‖ / ‖w‖ := add_le_add hCauchy le_rfl
    _ = (20 * (1 / 100) + ‖a‖) / ‖w‖ := by
          rw [div_div_eq_mul_div, ← add_div]; ring
    _ ≤ 1 / 2 := by
          rw [div_le_iff₀ hwpos]
          have h40 : 40 * (1 / 100 : ℝ) + 2 * ‖a‖ ≤ ‖w‖ := by
            have := le_trans hRA hwR; linarith
          linarith

end Work.Pert
