import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.exists_ball_subset_of_forall_mem
import Submission.Work.Pert.Ksub2.exists_ball_local_inverse

/-!
# `Work.Pert.Ksub2.f0_iterate_lipschitz`

**Amplification of a `φ₀`-walk under `f₀`.**  Let `d : ParabData f₀ D₀` be §4.1 data for a
parabolic germ `f₀`, `u ∈ QLeft ξ₀` a (repelling-side) point whose translate walk
`u, u+1, …, u+n` stays in `Dφ`, `Ce` an upper bound for `‖φ'‖` on the `ρe`-balls around the walk
points and `cc > 0` a lower bound for `‖φ'‖` on the `ρe`-ball around `u` (`u ∈ QLeft ξ₀ ⊆ Dφ`
and `Q_maps` already pin the *values*, so only the derivative bounds enter).  Then `f₀^[n]` is
Lipschitz with constant `2 Ce / cc` on a (small) ball around `φ₀ u`.

Why this is what the derivative bounds give: writing the local inverse of `φ` at `u` as `ψ`
(exists because `φ` is holomorphic near `u ∈ Dφ` and `‖φ' u‖ ≥ cc > 0`), for `‖z - φ u‖ < ρ` the
point `w := ψ z` satisfies `φ w = z`, `‖w - u‖ ≤ 2/cc ‖z - φ u‖`, and — by the Abel equation
`φ (t+1) = f₀ (φ t)` iterated along the walk — `f₀^[n] z = φ (w+n)`, `f₀^[n] (φ u) = φ (u+n)`.
The mean value theorem on the `ρe`-ball around `u+n` (where `‖φ'‖ ≤ Ce`) bounds
`‖φ (w+n) - φ (u+n)‖ ≤ Ce ‖w - u‖ ≤ (2 Ce / cc) ‖z - φ u‖`.

No differentiability of `f₀` is used: the statement is a statement about `φ` transported by the
Abel equation.  (The telescoped derivative identity
`(f₀^[n])' (φ u) = φ'(u+n)/φ'(u)` is the same inequality, read infinitesimally.)

## Contents

* `iterate_phi_of_mem`: the walk form `f₀^[n] (φ w) = φ (w+n)` of `ParabData.φ_abel`
  (a `ParabData`-specialisation of `Work.Pert.iterate_phi`).
* `f0_iterate_lipschitz`: the target.

Delegated pieces used: `Work.Pert.Ksub2.exists_ball_subset_of_forall_mem` (a single radius for the
finitely many walk points) and `Work.Pert.Ksub2.exists_ball_local_inverse` (local inverse with an
explicit Lipschitz bound).
-/

namespace Work.Pert.Ksub2

open MandelDim Filter
open scoped Topology

noncomputable section

/-- Iteration of the Abel equation `d.φ (w+1) = f₀ (d.φ w)` along the walk `w, w+1, …, w+n ⊆ Dφ`:
`f₀^[n] (d.φ w) = d.φ (w+n)`.  (Specialisation of `Work.Pert.iterate_phi` to `ParabData`.) -/
theorem iterate_phi_of_mem {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {w : ℂ}
    {n : ℕ} (hw : ∀ i : ℕ, i ≤ n → w + (i : ℂ) ∈ d.Dφ) :
    f₀^[n] (d.φ w) = d.φ (w + (n : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw' : ∀ i : ℕ, i ≤ n → w + (i : ℂ) ∈ d.Dφ := fun i hi => hw i (by omega)
    rw [Function.iterate_succ_apply', ih hw']
    have h1 : w + (n : ℂ) ∈ d.Dφ := hw n (by omega)
    have h2 : w + (n : ℂ) + 1 ∈ d.Dφ := by
      have := hw (n + 1) (by omega)
      rwa [show w + ((n + 1 : ℕ) : ℂ) = w + (n : ℂ) + 1 by push_cast; ring] at this
    have hcast : w + ((n + 1 : ℕ) : ℂ) = w + (n : ℂ) + 1 := by push_cast; ring
    rw [hcast, d.φ_abel (w + (n : ℂ)) h1 h2]

theorem f0_iterate_lipschitz {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {u : ℂ} (hu : u ∈ MandelDim.QLeft d.ξ₀) {n : ℕ}
    (hwalk : ∀ i : ℕ, i ≤ n → u + (i : ℂ) ∈ d.Dφ)
    {Ce cc ρe : ℝ} (hcc : 0 < cc) (hρe : 0 < ρe)
    (hCe : ∀ i : ℕ, i ≤ n → ∀ z : ℂ, ‖z - (u + (i : ℂ))‖ ≤ ρe → ‖deriv d.φ z‖ ≤ Ce)
    (hcc' : ∀ z : ℂ, ‖z - u‖ ≤ ρe → cc ≤ ‖deriv d.φ z‖) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, ‖z - d.φ u‖ < ρ →
      ‖f₀^[n] z - f₀^[n] (d.φ u)‖ ≤ (2 * Ce / cc) * ‖z - d.φ u‖ := by
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
  -- a single radius around the whole walk
  obtain ⟨r₁, hr₁, hr₁'⟩ := exists_ball_subset_of_forall_mem d.Dφ_open hwalk
  have hr : 0 < min r₁ ρe := lt_min hr₁ hρe
  refine ⟨min ρ₁ (min r₁ ρe * cc / 2), lt_min hρ₁ (by positivity), fun z hz => ?_⟩
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
  -- `w` can be walked: `w, w+1, …, w+n ∈ Dφ`
  have hmem : ∀ i : ℕ, i ≤ n → w + (i : ℂ) ∈ d.Dφ := by
    intro i hi
    have hb : Metric.ball (u + (i : ℂ)) r₁ ⊆ d.Dφ := hr₁' i hi
    have hdist : dist (w + (i : ℂ)) (u + (i : ℂ)) < r₁ := by
      rw [dist_eq_norm]
      have heq : w + (i : ℂ) - (u + (i : ℂ)) = w - u := by ring
      rw [heq]
      exact hwr
    exact hb (by rwa [Metric.mem_ball])
  -- both iterates are given by the Abel walk
  have hiter_w : f₀^[n] (d.φ w) = d.φ (w + (n : ℂ)) := iterate_phi_of_mem d hmem
  have hiter_u : f₀^[n] (d.φ u) = d.φ (u + (n : ℂ)) := iterate_phi_of_mem d hwalk
  have hCe_nn : 0 ≤ Ce := le_trans (norm_nonneg _) (hCe 0 (Nat.zero_le n) u (by simp [hρe.le]))
  -- mean value theorem at the far end of the walk
  have hMVT : ‖d.φ (w + (n : ℂ)) - d.φ (u + (n : ℂ))‖ ≤ Ce * ‖w - u‖ := by
    have hle : ∀ x ∈ Metric.ball (u + (n : ℂ)) (min r₁ ρe), ‖x - (u + (n : ℂ))‖ < ρe := by
      intro x hx
      have h1 : x ∈ Metric.ball (u + (n : ℂ)) ρe :=
        Metric.ball_subset_ball (min_le_right r₁ ρe) hx
      rwa [Metric.mem_ball, dist_eq_norm] at h1
    have hball2 : Metric.ball (u + (n : ℂ)) (min r₁ ρe) ⊆ d.Dφ :=
      subset_trans (Metric.ball_subset_ball (min_le_left _ _)) (hr₁' n le_rfl)
    have hmem_w : w + (n : ℂ) ∈ Metric.ball (u + (n : ℂ)) (min r₁ ρe) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hww : w + (n : ℂ) - (u + (n : ℂ)) = w - u := by ring
      rw [hww]
      exact hwu
    have h := (convex_ball (u + (n : ℂ)) (min r₁ ρe)).norm_image_sub_le_of_norm_deriv_le
      (f := d.φ) (C := Ce) (x := u + (n : ℂ)) (y := w + (n : ℂ))
      (fun x hx => d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds (hball2 hx)))
      (fun x hx => hCe n le_rfl x (le_of_lt (hle x hx)))
      (by rw [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]; exact hr)
      hmem_w
    simpa using h
  calc ‖f₀^[n] z - f₀^[n] (d.φ u)‖
      = ‖d.φ (w + (n : ℂ)) - d.φ (u + (n : ℂ))‖ := by rw [← hφw, hiter_w, hiter_u]
    _ ≤ Ce * ‖w - u‖ := hMVT
    _ ≤ Ce * (2 * cc⁻¹ * ‖z - d.φ u‖) := mul_le_mul_of_nonneg_left hwlip hCe_nn
    _ = (2 * Ce / cc) * ‖z - d.φ u‖ := by ring

end

end Work.Pert.Ksub2
