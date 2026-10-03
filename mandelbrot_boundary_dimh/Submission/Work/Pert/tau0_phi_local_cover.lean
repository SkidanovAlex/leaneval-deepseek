import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Basic
import Submission.Work.Pert.deriv_psi0_close
import Submission.Work.Pert.image_cover
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Pert.phi_ne_zero_far

/-!
# `Work.Pert.tau0_phi_local_cover`

Shishikura's Appendix A.4 (the "fourth quadrant" covering estimate, (4.2.x)): far out in the
sector `QLeft ξ₀` the map `Φ = tau0 ∘ φ` (i.e. `φ*`, the reciprocal of the perturbed Fatou
coordinate) covers a full ball of radius `‖w‖/40` around `Φ w`, for `w` of large norm whose
quarter-ball still lies in the sector.

The asymptotic `φ_asymp : tau0 (φ w) = w + a log (-w) + b + o(1)` says that `Φ` is a "quasi
translation" at scale `‖w‖`: it moves points by the slowly varying amount `a log (-w) + b`, which
is essentially constant on a ball of radius `‖w‖/8` (its gradient is `O(1/‖w‖)`).  Hence the
displacement of `Φ` from its *centre* `Φ w` is a contraction of ratio `1/2` on that ball and the
Rouché-based covering lemma `Work.Pert.image_cover_centered` applies, giving

`ball (Φ w) (‖w‖/32) ⊆ Φ '' closedBall w (‖w‖/8) ⊆ Φ '' QLeft ξ₀`.

Since `‖w‖/40 ≤ ‖w‖/32` this is the claim.

Two ingredients are delegated/proved separately:

* `Work.Pert.deriv_tau0_phi_close_on_ball_aux` (below): the C¹ estimate
  `‖deriv (tau0 ∘ φ) - 1‖ ≤ 1/2` on the *whole* ball `closedBall w (‖w‖/8)`; it is the
  `Work.Pert.deriv_psi0_close` estimate transferred from the single point `w` to the ball, the
  only point being that the smaller ball `ball u (‖u‖/10)` of the pointwise statement still sits
  inside `ball w (‖w‖/4) ⊆ QLeft ξ₀` (numerically `19/80 < 1/4`).
* `Work.Pert.phi_ne_zero_far`: `φ ≠ 0` on that ball, which (with `φ_holo` and the openness of
  `Dφ`) gives differentiability of `tau0 ∘ φ` there.
-/

namespace Work.Pert

open Metric Set

noncomputable section

/-- The derivative of `tau0 ∘ φ` is within `1/2` of `1` on the whole ball `closedBall w (‖w‖/8)`,
for `w` far out in Shishikura's sector with room `ball w (‖w‖/4) ⊆ QLeft ξ₀`.

This is `Work.Pert.deriv_psi0_close` applied at each point `u` of the smaller ball: such a `u`
still satisfies `‖u‖ ≥ 7‖w‖/8` and `ball u (‖u‖/10) ⊆ ball w (19‖w‖/80) ⊆ QLeft ξ₀`. -/
theorem deriv_tau0_phi_close_on_ball_aux {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, w ∈ MandelDim.QLeft d.ξ₀ → R ≤ ‖w‖ →
      Metric.ball w (‖w‖ / 4) ⊆ MandelDim.QLeft d.ξ₀ →
      ∀ u ∈ Metric.closedBall w (‖w‖ / 8),
        ‖deriv (fun u : ℂ => MandelDim.tau0 (d.φ u)) u - 1‖ ≤ 1 / 2 := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := deriv_psi0_close d
  refine ⟨8 * R₀ + 1, by linarith, ?_⟩
  intro w hwQ hwR hball u hu
  have hR0w : R₀ ≤ ‖w‖ := by linarith
  have hwpos : 0 < ‖w‖ := by linarith
  -- `u` is at least `7/8` of `w` in norm, and at most `9/8`
  have h1 : ‖u - w‖ ≤ ‖w‖ / 8 := by
    have h := Metric.mem_closedBall.mp hu
    rwa [dist_eq_norm] at h
  have hu_ge : 7 * ‖w‖ / 8 ≤ ‖u‖ := by
    have h := norm_add_le (w - u) u
    rw [sub_add_cancel] at h
    have h2 : ‖w - u‖ = ‖u - w‖ := norm_sub_rev w u
    linarith
  have hu_le : ‖u‖ ≤ 9 * ‖w‖ / 8 := by
    have h := norm_add_le (u - w) w
    rw [sub_add_cancel] at h
    linarith
  have huQ : u ∈ MandelDim.QLeft d.ξ₀ :=
    hball (Metric.closedBall_subset_ball (by linarith) hu)
  have hnorm : R₀ ≤ ‖u‖ := by linarith
  refine hR₀ u huQ hnorm ?_
  -- the `‖u‖/10`-ball of the pointwise statement stays in `ball w (‖w‖/4)`
  intro v hv
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  have hv1 : ‖v - u‖ < ‖u‖ / 10 := by
    have h := Metric.mem_ball.mp hv
    rwa [dist_eq_norm] at h
  have h3 : ‖v - w‖ ≤ ‖v - u‖ + ‖u - w‖ := by
    have h := norm_add_le (v - u) (u - w)
    rwa [show v - u + (u - w) = v - w by ring] at h
  have h4 : ‖u‖ / 10 ≤ 9 * ‖w‖ / 80 := by linarith
  linarith

/-- Local covering of the `tau0 ∘ φ`-image: for `w` deep in Shishikura's sector `QLeft ξ₀` (with
room `ball w (‖w‖/4) ⊆ QLeft ξ₀`), the map `u ↦ tau0 (φ u)` maps a neighbourhood of `w` onto a
ball of radius `‖w‖/40` around `tau0 (φ w)`.  (This is `image_cover` applied to the C¹ estimate
`‖(tau0 ∘ φ)' - 1‖ ≤ 1/2` of `Work.Pert.deriv_psi0_close` together with the asymptotic
`tau0 (φ w) = w + a log(-w) + b + o(1)`.) -/
theorem tau0_phi_local_cover {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, w ∈ MandelDim.QLeft d.ξ₀ → R ≤ ‖w‖ →
      Metric.ball w (‖w‖ / 4) ⊆ MandelDim.QLeft d.ξ₀ →
      Metric.ball (MandelDim.tau0 (d.φ w)) (‖w‖ / 40) ⊆
        (fun u : ℂ => MandelDim.tau0 (d.φ u)) '' MandelDim.QLeft d.ξ₀ := by
  obtain ⟨R₁, hR₁pos, hR₁⟩ := deriv_tau0_phi_close_on_ball_aux d
  obtain ⟨R₂, hR₂pos, hR₂⟩ := phi_ne_zero_far d
  refine ⟨max R₁ R₂, lt_max_of_lt_left hR₁pos, ?_⟩
  intro w hwQ hwR hball
  have hR1w : R₁ ≤ ‖w‖ := le_trans (le_max_left _ _) hwR
  have hR2w : R₂ ≤ ‖w‖ := le_trans (le_max_right _ _) hwR
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hR₁pos hR1w
  -- `tau0 ∘ φ` is differentiable on `closedBall w (‖w‖/8)`
  have hdiff : ∀ ζ ∈ Metric.closedBall w (‖w‖ / 8),
      DifferentiableAt ℂ (fun u : ℂ => MandelDim.tau0 (d.φ u)) ζ := by
    intro ζ hζ
    have hζball : ζ ∈ Metric.ball w (‖w‖ / 4) :=
      Metric.closedBall_subset_ball (by linarith) hζ
    have hζQ : ζ ∈ MandelDim.QLeft d.ξ₀ := hball hζball
    have hne : d.φ ζ ≠ 0 := hR₂ w hwQ hR2w hball ζ hζball
    have hphi : DifferentiableAt ℂ d.φ ζ :=
      d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds (d.Q_sub hζQ))
    have htau : DifferentiableAt ℂ MandelDim.tau0 (d.φ ζ) :=
      (differentiableAt_const (-1)).div differentiableAt_id (by simpa [MandelDim.tau0] using hne)
    simpa [Function.comp_def] using htau.comp ζ hphi
  -- Rouché/Euclidean covering around the centre `w`
  have hcov := image_cover_centered (Φ := fun u : ℂ => MandelDim.tau0 (d.φ u))
    (z₀ := w) (r := ‖w‖ / 8) (by linarith) hdiff (hR₁ w hwQ hR1w hball)
  intro x hx
  have hx' : x ∈ Metric.ball (MandelDim.tau0 (d.φ w)) ((‖w‖ / 8) / 4) :=
    Metric.ball_subset_ball (by linarith) hx
  obtain ⟨u, hu, hueq⟩ := hcov hx'
  exact ⟨u, hball (Metric.closedBall_subset_ball (by linarith) hu), hueq⟩

end

end Work.Pert
