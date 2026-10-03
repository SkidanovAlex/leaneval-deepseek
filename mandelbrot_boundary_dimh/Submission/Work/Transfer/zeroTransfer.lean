import Mathlib
import Submission.Work.Transfer.Setup
import Submission.Work.Transfer.exists_sphere_le_norm
import Submission.Work.Transfer.exists_zero_of_norm_lower_bound

/-!
# The "zero transfer" step

Given a holomorphic motion `phi` of the IFS and a parameter `c_s` at which the `m`-th critical
orbit point satisfies `critOrbit m c_s = phi c_s w`, and given that the function
`c ↦ critOrbit m c - phi c w` is *not* identically zero on the base ball (non-degeneracy), every
code `u` agreeing with `w` on a sufficiently long initial segment realises the critical orbit
somewhere in a ball around `c_s`.

This is step 3 of the transfer argument of `Work.Transfer.transfer`.
-/

namespace Work.Transfer

open Set Metric Filter Topology
open Classical

/-- **Zero transfer.** With `e_w (c) = critOrbit m c - phi c w` not identically zero on
`ball c₀ ρ` and vanishing at `c_s`, there is `k₀` such that for every code `u` agreeing with `w` on
the first `k₀` letters the function `e_u` has a zero in `ball c_s R`.

The proof picks a circle around `c_s` inside `ball c_s R` on which `e_w` is bounded below by some
`δ > 0` (isolated zeros of a non-zero holomorphic function); the contraction estimate of the
motion then makes `e_u` uniformly `< δ/4`-close to `e_w` on that circle (and at `c_s`, where `e_w`
vanishes).  The minimum modulus principle (`exists_zero_of_norm_lower_bound`) turns
"small at the centre, large on the boundary" into the existence of a zero. -/
theorem zeroTransfer {N : ℕ} {c₀ : ℂ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {ρ a : ℝ}
    {phi : ℂ → (ℕ → Fin N) → ℂ} (hρ : 0 < ρ) (hMD : Work.Transfer.MotionData c₀ N τ n p ρ a phi)
    {m : ℕ} {w : ℕ → Fin N}
    (hne : ∃ z ∈ Metric.ball c₀ ρ, Work.Transfer.critOrbit m z ≠ phi z w)
    {R : ℝ} (hR : 0 < R) {c_s : ℂ} (hcs : c_s ∈ Metric.ball c₀ ρ)
    (hbsub : Metric.ball c_s R ⊆ Metric.ball c₀ ρ)
    (hz : Work.Transfer.critOrbit m c_s = phi c_s w) :
    ∃ k₀ : ℕ, ∀ u : ℕ → Fin N, (∀ j < k₀, u j = w j) →
      ∃ c ∈ Metric.ball c_s R, Work.Transfer.critOrbit m c = phi c u := by
  -- `e_w` is holomorphic on the base ball and does not vanish identically there.
  have hdiff_ew : DifferentiableOn ℂ (fun c => critOrbit m c - phi c w) (Metric.ball c₀ ρ) :=
    (differentiable_critOrbit m).differentiableOn.sub (hMD.diff w)
  have han_ew : AnalyticOnNhd ℂ (fun c => critOrbit m c - phi c w) (Metric.ball c₀ ρ) :=
    hdiff_ew.analyticOnNhd Metric.isOpen_ball
  have hne_ew : ∃ z ∈ Metric.ball c₀ ρ, (fun c => critOrbit m c - phi c w) z ≠ 0 := by
    obtain ⟨z, hz', hzne⟩ := hne
    exact ⟨z, hz', sub_ne_zero.mpr hzne⟩
  -- A circle around `c_s` inside `ball c_s R` on which `e_w` is bounded below by some `δ > 0`.
  obtain ⟨r, hrIoo, δ, hδpos, hδbound⟩ :=
    exists_sphere_le_norm hR hcs hbsub han_ew hne_ew
  obtain ⟨hr0, hrR⟩ := hrIoo
  -- The contraction estimate of the motion.
  obtain ⟨C, θ, hθ0, hθ1, hcontr⟩ := hMD.contract
  have htend : Tendsto (fun k : ℕ => C * θ ^ k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => θ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
    have h2 := h1.const_mul C
    simpa using h2
  -- A length `k₀` beyond which the contraction makes `|phi · u - phi · w| < δ/4`.
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, C * θ ^ k₀ < δ / 4 := by
    have hpos : (0 : ℝ) < δ / 4 := by linarith
    have hev : ∀ᶠ k in atTop, C * θ ^ k < δ / 4 := (tendsto_order.1 htend).2 (δ / 4) hpos
    obtain ⟨k, hk⟩ := eventually_atTop.1 hev
    exact ⟨k, hk k le_rfl⟩
  refine ⟨k₀, fun u hu => ?_⟩
  -- `e_u` is small at the centre ...
  have hcu : ‖critOrbit m c_s - phi c_s u‖ < δ / 2 / 2 := by
    have h1 : ‖phi c_s u - phi c_s w‖ ≤ C * θ ^ k₀ := hcontr c_s hcs k₀ u w hu
    have h2 : critOrbit m c_s - phi c_s u = -(phi c_s u - phi c_s w) := by rw [hz]; ring
    rw [h2, norm_neg]
    linarith
  have hdcc_eu : DiffContOnCl ℂ (fun c => critOrbit m c - phi c u) (Metric.closedBall c_s r) := by
    apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact ((differentiable_critOrbit m).differentiableOn.sub (hMD.diff u)).mono
      (fun z hz => hbsub (Metric.closedBall_subset_ball hrR hz))
  -- ... and bounded below by `δ/2` on the circle.
  have hgb : ∀ z ∈ Metric.sphere c_s r, δ / 2 ≤ ‖critOrbit m z - phi z u‖ := by
    intro z hz
    have hzball : z ∈ Metric.ball c₀ ρ :=
      hbsub (Metric.closedBall_subset_ball hrR (Metric.sphere_subset_closedBall hz))
    have h1 : ‖phi z u - phi z w‖ ≤ C * θ ^ k₀ := hcontr z hzball k₀ u w hu
    have h2 : δ ≤ ‖critOrbit m z - phi z w‖ := hδbound z hz
    have h3 : ‖critOrbit m z - phi z w‖ ≤ ‖critOrbit m z - phi z u‖ + ‖phi z u - phi z w‖ := by
      have heq : critOrbit m z - phi z w = (critOrbit m z - phi z u) + (phi z u - phi z w) := by ring
      rw [heq]; exact norm_add_le _ _
    linarith
  obtain ⟨c, hc_mem, hc_zero⟩ :=
    exists_zero_of_norm_lower_bound hr0 (by linarith : (0:ℝ) < δ/2) hdcc_eu hgb hcu
  exact ⟨c, Metric.closedBall_subset_ball hrR hc_mem, sub_eq_zero.mp hc_zero⟩

end Work.Transfer
