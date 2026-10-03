import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.L62LD.tube_data`

A compactum `K ⊆ hd.Bl` of the lower horn of a horn datum `hd : HornData d` carries a *tube*
`K + closedBall 0 δ ⊆ hd.Bl` on which the derivative of `d.E` is uniformly bounded — and since
`deriv (d.E - β) = deriv d.E`, the bound is uniform in the parameter `β`.

This is the "tube" input used by the lower-end head of Lemma 6.2: `δ` is the tube radius on which
the perturbed horn map is compared with `d.E`, and `Δ` the Lipschitz constant of `d.E - β` there.
-/

namespace Work.L62LD

open Classical MandelDim Set Metric Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- `d.E = Φ ∘ φ` is holomorphic on the lower horn `hd.Bl ⊆ d.DE`. -/
theorem differentiableOn_E_Bl_tube (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) :
    DifferentiableOn ℂ d.E hd.Bl :=
  d.Φ_holo.comp (d.φ_holo.mono fun _ hw => (hd.sub (Or.inr hw)).1)
    fun _ hw => (hd.sub (Or.inr hw)).2

/-- **The tube data of the lower end.**  For a compactum `K ⊆ hd.Bl` there are `δ > 0`, `Δ ≥ 1`
and `R ≥ 0` with `K ⊆ closedBall 0 R`, the tube `K + closedBall 0 δ` contained in `hd.Bl`, and
`‖deriv (fun w => d.E w - β)‖ ≤ Δ` on that tube, uniformly in `β`. -/
theorem tube_data {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {K : Set ℂ} (hKc : IsCompact K) (hKBl : K ⊆ hd.Bl) :
    ∃ (δ Δ R : ℝ), 0 < δ ∧ 1 ≤ Δ ∧ 0 ≤ R ∧ K ⊆ Metric.closedBall 0 R ∧
      (∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ → v + z ∈ hd.Bl) ∧
      (∀ β : ℂ, ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ →
        ‖deriv (fun w => d.E w - β) (v + z)‖ ≤ Δ) := by
  -- `d.E` is holomorphic on the lower horn
  have hE : DifferentiableOn ℂ d.E hd.Bl := differentiableOn_E_Bl_tube d hd
  -- a closed tube around `K` inside the open horn
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hKc.exists_cthickening_subset_open hd.Bl_open hKBl
  -- that tube is compact, so `deriv d.E` is bounded on it
  have hCpt : IsCompact (Metric.cthickening δ₁ K) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨Metric.isClosed_cthickening, hKc.isBounded.cthickening⟩
  have hCont : ContinuousOn (deriv d.E) (Metric.cthickening δ₁ K) :=
    (hE.deriv hd.Bl_open).continuousOn.mono hδ₁
  obtain ⟨C, hC⟩ := hCpt.exists_bound_of_continuousOn hCont
  obtain ⟨M, hM⟩ := hKc.isBounded.exists_norm_le
  -- the membership of `v + z` for `‖z‖ ≤ δ₁ / 2` in the tube of radius `δ₁`
  have hmem : ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ₁ / 2 → v + z ∈ Metric.cthickening δ₁ K := by
    intro v hv z hz
    have h1 : v + z ∈ Metric.cthickening (δ₁ / 2) K :=
      Metric.closedBall_subset_cthickening hv (δ₁ / 2) (by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hzv : v + z - v = z := by ring
        rw [hzv]
        exact hz)
    exact Metric.cthickening_mono (by linarith) K h1
  refine ⟨δ₁ / 2, max 1 C, max M 0, by linarith, le_max_left _ _, le_max_right _ _, ?_, ?_, ?_⟩
  · -- `K` lies in a ball
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans (hM x hx) (le_max_left _ _)
  · -- the tube of radius `δ₁ / 2` is contained in `hd.Bl`
    intro v hv z hz
    exact hδ₁ (hmem v hv z hz)
  · -- the derivative bound, uniform in `β`
    intro β v hv z hz
    rw [deriv_sub_const β]
    exact le_trans (hC _ (hmem v hv z hz)) (le_max_right _ _)

end

end Work.L62LD
