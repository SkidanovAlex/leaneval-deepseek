import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.f0_iterate_lipschitz

/-!
# `Work.Pert.Ksub2.f0_iterate_lipschitz_uniform_D`

**Uniform-in-the-number-of-steps amplification of a `φ₀`-walk under `f₀`, with the domain
`d.Dφ` carried explicitly.**

This is the `Dφ`-carrying variant of `Work.Pert.Ksub2.f0_iterate_lipschitz_uniform`: here the
derivative bounds `hCe` (upper) and `hcc'` (lower) are required only on points of `d.Dφ`, and the
fact that the `ρe`-balls around the walk points `u, u+1, …, u+N` lie in `d.Dφ` is an explicit
hypothesis `hball` (rather than being produced from openness of `Dφ` by compactness).

The mathematics is the same: the local inverse `ψ` of `φ` at `u` gives, for
`‖z - φ u‖ < ρ`, a point `w := ψ z` with `φ w = z` and `‖w - u‖ ≤ 2 cc⁻¹ ‖z - φ u‖`; the Abel
equation transported along the walks `w, w+1, …, w+k` and `u, u+1, …, u+k` identifies
`f₀^[k] z = φ (w+k)`, `f₀^[k] (φ u) = φ (u+k)`, and the mean value theorem on the `ρe`-ball around
`u+k` (all of whose points are in `d.Dφ`, by `hball`) bounds the difference by `Ce ‖w-u‖`.

The only difference from the base version is that `hball` replaces
`exists_ball_subset_of_forall_mem`, and the domain memberships are fed to `hCe`/`hcc'`.
-/

namespace Work.Pert.Ksub2

open MandelDim Filter
open scoped Topology

noncomputable section

theorem f0_iterate_lipschitz_uniform_D {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {u : ℂ} (hu : u ∈ MandelDim.QLeft d.ξ₀) {N : ℕ}
    (hwalk : ∀ i : ℕ, i ≤ N → u + (i : ℂ) ∈ d.Dφ)
    {Ce cc ρe : ℝ} (hcc : 0 < cc) (hρe : 0 < ρe)
    (hball : ∀ i : ℕ, i ≤ N → Metric.ball (u + (i : ℂ)) ρe ⊆ d.Dφ)
    (hCe : ∀ i : ℕ, i ≤ N → ∀ z : ℂ, z ∈ d.Dφ → ‖z - (u + (i : ℂ))‖ ≤ ρe → ‖deriv d.φ z‖ ≤ Ce)
    (hcc' : ∀ z : ℂ, z ∈ d.Dφ → ‖z - u‖ ≤ ρe → cc ≤ ‖deriv d.φ z‖) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : ℕ, k ≤ N → ∀ z : ℂ, ‖z - d.φ u‖ < ρ →
      ‖f₀^[k] z - f₀^[k] (d.φ u)‖ ≤ (2 * Ce / cc) * ‖z - d.φ u‖ := by
  -- `φ` is holomorphic near `u` with nonvanishing derivative there, so it has a local inverse
  have huDφ : u ∈ d.Dφ := d.Q_sub hu
  have hderiv_ge : cc ≤ ‖deriv d.φ u‖ := hcc' u huDφ (by simp [hρe.le])
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
  refine ⟨min ρ₁ (ρe * cc / 2), lt_min hρ₁ (by positivity), fun k hk z hz => ?_⟩
  obtain ⟨hz1, hz2⟩ := lt_min_iff.mp hz
  obtain ⟨hφψ, hψz⟩ := h₁ z hz1
  set w : ℂ := ψ z with hwdef
  have hφw : d.φ w = z := by rw [hwdef]; exact hφψ
  have hwlip : ‖w - u‖ ≤ 2 * cc⁻¹ * ‖z - d.φ u‖ := hψz
  have hconst : 2 * cc⁻¹ * (ρe * cc / 2) = ρe := by field_simp
  have hwu : ‖w - u‖ < ρe := by
    calc ‖w - u‖ ≤ 2 * cc⁻¹ * ‖z - d.φ u‖ := hwlip
      _ < 2 * cc⁻¹ * (ρe * cc / 2) :=
          mul_lt_mul_of_pos_left hz2 (by positivity)
      _ = ρe := hconst
  -- the walk points of the truncated length `k`
  have hwalkk : ∀ i : ℕ, i ≤ k → u + (i : ℂ) ∈ d.Dφ := fun i hi => hwalk i (le_trans hi hk)
  -- `w` can be walked: `w, w+1, …, w+k ∈ Dφ` (the `ρe`-balls around the walk are in `Dφ`)
  have hmem : ∀ i : ℕ, i ≤ k → w + (i : ℂ) ∈ d.Dφ := by
    intro i hi
    have hb : Metric.ball (u + (i : ℂ)) ρe ⊆ d.Dφ := hball i (le_trans hi hk)
    have hdist : dist (w + (i : ℂ)) (u + (i : ℂ)) < ρe := by
      rw [dist_eq_norm]
      have heq : w + (i : ℂ) - (u + (i : ℂ)) = w - u := by ring
      rw [heq]
      exact hwu
    exact hb (by rwa [Metric.mem_ball])
  -- both iterates are given by the Abel walk
  have hiter_w : f₀^[k] (d.φ w) = d.φ (w + (k : ℂ)) := iterate_phi_of_mem d hmem
  have hiter_u : f₀^[k] (d.φ u) = d.φ (u + (k : ℂ)) := iterate_phi_of_mem d hwalkk
  have hCe_nn : 0 ≤ Ce :=
    le_trans (norm_nonneg _) (hCe 0 (Nat.zero_le N) u huDφ (by simp [hρe.le]))
  -- mean value theorem at the far end of the walk
  have hMVT : ‖d.φ (w + (k : ℂ)) - d.φ (u + (k : ℂ))‖ ≤ Ce * ‖w - u‖ := by
    have hball2 : Metric.ball (u + (k : ℂ)) ρe ⊆ d.Dφ := hball k hk
    have hmem_w : w + (k : ℂ) ∈ Metric.ball (u + (k : ℂ)) ρe := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hww : w + (k : ℂ) - (u + (k : ℂ)) = w - u := by ring
      rw [hww]
      exact hwu
    have h := (convex_ball (u + (k : ℂ)) ρe).norm_image_sub_le_of_norm_deriv_le
      (f := d.φ) (C := Ce) (x := u + (k : ℂ)) (y := w + (k : ℂ))
      (fun x hx => d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds (hball2 hx)))
      (fun x hx => hCe k hk x (hball2 hx)
        (by rw [Metric.mem_ball, dist_eq_norm] at hx; exact le_of_lt hx))
      (by rw [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]; exact hρe)
      hmem_w
    simpa using h
  calc ‖f₀^[k] z - f₀^[k] (d.φ u)‖
      = ‖d.φ (w + (k : ℂ)) - d.φ (u + (k : ℂ))‖ := by rw [← hφw, hiter_w, hiter_u]
    _ ≤ Ce * ‖w - u‖ := hMVT
    _ ≤ Ce * (2 * cc⁻¹ * ‖z - d.φ u‖) := mul_le_mul_of_nonneg_left hwlip hCe_nn
    _ = (2 * Ce / cc) * ‖z - d.φ u‖ := by ring

end

end Work.Pert.Ksub2
