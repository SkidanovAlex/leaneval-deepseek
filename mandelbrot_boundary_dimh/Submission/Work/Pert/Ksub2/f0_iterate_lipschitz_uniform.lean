import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.f0_iterate_lipschitz

/-!
# `Work.Pert.Ksub2.f0_iterate_lipschitz_uniform`

**Uniform-in-the-number-of-steps amplification of a `φ₀`-walk under `f₀`.**

Let `d : ParabData f₀ D₀` be the §4.1 data of a parabolic germ, `u ∈ QLeft ξ₀` a (repelling side)
point whose translate walk `u, u+1, …, u+N` stays in `Dφ`, `Ce` an upper bound for `‖φ'‖` on the
`ρe`-balls around the walk points and `cc > 0` a lower bound for `‖φ'‖` on the `ρe`-ball around
`u`.  Then there is a **single** radius `ρ > 0` (depending on `N`, but not on the step count `k`)
such that for every `k ≤ N` the iterate `f₀^[k]` is Lipschitz with constant `2 Ce / cc` on the ball
of radius `ρ` around `φ₀ u`.

The mathematics is the same as for the pointwise version `f0_iterate_lipschitz`; the only
difference is that the (finitely many) walk points used to produce the radius are *all* of
`u, …, u+N`, so that the radius survives every `k ≤ N`:

* the local inverse `ψ` of `φ` at `u` (which exists because `φ` is holomorphic near `u ∈ Dφ` and
  `‖φ' u‖ ≥ cc > 0`) satisfies `‖ψ z - u‖ ≤ 2 cc⁻¹ ‖z - φ u‖`, so for `‖z - φ u‖ < ρ` the point
  `w := ψ z` lies in the ball of radius `r₁` around `u` and hence `w, w+1, …, w+k ∈ Dφ`;
* the Abel equation `φ (t+1) = f₀ (φ t)` iterated along those walks gives
  `f₀^[k] z = φ (w+k)` and `f₀^[k] (φ u) = φ (u+k)`;
* the mean value theorem on the `ρe`-ball around `u+k` (where `‖φ'‖ ≤ Ce`) bounds
  `‖φ (w+k) - φ (u+k)‖ ≤ Ce ‖w-u‖ ≤ (2 Ce / cc) ‖z - φ u‖`.

No differentiability of `f₀` is used: the statement is a statement about `φ` transported by the
Abel equation.
-/

namespace Work.Pert.Ksub2

open MandelDim Filter
open scoped Topology

noncomputable section

theorem f0_iterate_lipschitz_uniform {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {u : ℂ} (hu : u ∈ MandelDim.QLeft d.ξ₀) {N : ℕ}
    (hwalk : ∀ i : ℕ, i ≤ N → u + (i : ℂ) ∈ d.Dφ)
    {Ce cc ρe : ℝ} (hcc : 0 < cc) (hρe : 0 < ρe)
    (hCe : ∀ i : ℕ, i ≤ N → ∀ z : ℂ, ‖z - (u + (i : ℂ))‖ ≤ ρe → ‖deriv d.φ z‖ ≤ Ce)
    (hcc' : ∀ z : ℂ, ‖z - u‖ ≤ ρe → cc ≤ ‖deriv d.φ z‖) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : ℕ, k ≤ N → ∀ z : ℂ, ‖z - d.φ u‖ < ρ →
      ‖f₀^[k] z - f₀^[k] (d.φ u)‖ ≤ (2 * Ce / cc) * ‖z - d.φ u‖ := by
  -- `φ` is holomorphic near `u` with nonvanishing derivative there, so it has a local inverse
  have huDφ : u ∈ d.Dφ := d.Q_sub hu
  have hderiv_ge : cc ≤ ‖deriv d.φ u‖ := hcc' u (by simp [hρe.le])
  have hne : deriv d.φ u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hderiv_ge
    linarith
  have hanal : AnalyticAt ℂ d.φ u := d.φ_holo.analyticAt (d.Dφ_open.mem_nhds huDφ)
  have hs : HasStrictDerivAt d.φ (deriv d.φ u) u := hanal.hasStrictDerivAt
  set ψ : ℂ → ℂ := hs.localInverse d.φ (deriv d.φ u) u hne with hψdef
  have hψd : HasDerivAt ψ ((deriv d.φ u))⁻¹ (d.φ u) := (hs.to_localInverse hne).hasDerivAt
  have hψu : ψ (d.φ u) = u := (hs.eventually_left_inverse hne).self_of_nhds
  have hψright : ∀ᶠ z in nhds (d.φ u), d.φ (ψ z) = z := hs.eventually_right_inverse hne
  -- the inverse of the derivative is bounded by `1/cc`
  have hA : ‖((deriv d.φ u))⁻¹‖ ≤ cc⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hcc hderiv_ge
  obtain ⟨ρ₁, hρ₁, h₁⟩ :=
    exists_ball_local_inverse (φ := d.φ) (ψ := ψ) hψu hψright hψd (inv_pos.mpr hcc) hA
  -- a single radius around the WHOLE walk `u, u+1, …, u+N`
  obtain ⟨r₁, hr₁, hr₁'⟩ := exists_ball_subset_of_forall_mem d.Dφ_open hwalk
  have hr : 0 < min r₁ ρe := lt_min hr₁ hρe
  refine ⟨min ρ₁ (min r₁ ρe * cc / 2), lt_min hρ₁ (by positivity), fun k hk z hz => ?_⟩
  obtain ⟨hz1, hz2⟩ := lt_min_iff.mp hz
  obtain ⟨hφψ, hψz⟩ := h₁ z hz1
  set w : ℂ := ψ z with hwdef
  have hφw : d.φ w = z := by rw [hwdef]; exact hφψ
  have hwlip : ‖w - u‖ ≤ 2 * cc⁻¹ * ‖z - d.φ u‖ := hψz
  have hconst : 2 * cc⁻¹ * (min r₁ ρe * cc / 2) = min r₁ ρe := by field_simp
  have hwu : ‖w - u‖ < min r₁ ρe := by
    calc ‖w - u‖ ≤ 2 * cc⁻¹ * ‖z - d.φ u‖ := hwlip
      _ < 2 * cc⁻¹ * (min r₁ ρe * cc / 2) :=
          mul_lt_mul_of_pos_left hz2 (by positivity)
      _ = min r₁ ρe := hconst
  have hwr : ‖w - u‖ < r₁ := lt_of_lt_of_le hwu (min_le_left _ _)
  -- the walk for the truncated length `k` (all points are among the `N + 1` walk points)
  have hwalkk : ∀ i : ℕ, i ≤ k → u + (i : ℂ) ∈ d.Dφ := fun i hi => hwalk i (le_trans hi hk)
  -- `w` can be walked: `w, w+1, …, w+k ∈ Dφ`
  have hmem : ∀ i : ℕ, i ≤ k → w + (i : ℂ) ∈ d.Dφ := by
    intro i hi
    have hb : Metric.ball (u + (i : ℂ)) r₁ ⊆ d.Dφ := hr₁' i (le_trans hi hk)
    have hdist : dist (w + (i : ℂ)) (u + (i : ℂ)) < r₁ := by
      rw [dist_eq_norm]
      have heq : w + (i : ℂ) - (u + (i : ℂ)) = w - u := by ring
      rw [heq]
      exact hwr
    exact hb (by rwa [Metric.mem_ball])
  -- both iterates are given by the Abel walk
  have hiter_w : f₀^[k] (d.φ w) = d.φ (w + (k : ℂ)) := iterate_phi_of_mem d hmem
  have hiter_u : f₀^[k] (d.φ u) = d.φ (u + (k : ℂ)) := iterate_phi_of_mem d hwalkk
  have hCe_nn : 0 ≤ Ce := le_trans (norm_nonneg _) (hCe 0 (Nat.zero_le N) u (by simp [hρe.le]))
  -- mean value theorem at the far end of the walk
  have hMVT : ‖d.φ (w + (k : ℂ)) - d.φ (u + (k : ℂ))‖ ≤ Ce * ‖w - u‖ := by
    have hle : ∀ x ∈ Metric.ball (u + (k : ℂ)) (min r₁ ρe), ‖x - (u + (k : ℂ))‖ < ρe := by
      intro x hx
      have h1 : x ∈ Metric.ball (u + (k : ℂ)) ρe :=
        Metric.ball_subset_ball (min_le_right r₁ ρe) hx
      rwa [Metric.mem_ball, dist_eq_norm] at h1
    have hball2 : Metric.ball (u + (k : ℂ)) (min r₁ ρe) ⊆ d.Dφ :=
      subset_trans (Metric.ball_subset_ball (min_le_left _ _)) (hr₁' k hk)
    have hmem_w : w + (k : ℂ) ∈ Metric.ball (u + (k : ℂ)) (min r₁ ρe) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hww : w + (k : ℂ) - (u + (k : ℂ)) = w - u := by ring
      rw [hww]
      exact hwu
    have h := (convex_ball (u + (k : ℂ)) (min r₁ ρe)).norm_image_sub_le_of_norm_deriv_le
      (f := d.φ) (C := Ce) (x := u + (k : ℂ)) (y := w + (k : ℂ))
      (fun x hx => d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds (hball2 hx)))
      (fun x hx => hCe k hk x (le_of_lt (hle x hx)))
      (by rw [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]; exact hr)
      hmem_w
    simpa using h
  calc ‖f₀^[k] z - f₀^[k] (d.φ u)‖
      = ‖d.φ (w + (k : ℂ)) - d.φ (u + (k : ℂ))‖ := by rw [← hφw, hiter_w, hiter_u]
    _ ≤ Ce * ‖w - u‖ := hMVT
    _ ≤ Ce * (2 * cc⁻¹ * ‖z - d.φ u‖) := mul_le_mul_of_nonneg_left hwlip hCe_nn
    _ = (2 * Ce / cc) * ‖z - d.φ u‖ := by ring

end

end Work.Pert.Ksub2
