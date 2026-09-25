import Mathlib

namespace Work.CR.Flat.Cauchy

/-- The differential of a `C¹` function on `ℂⁿ = Fin n → ℂ` that vanishes outside the open half-size polydisc is bounded.
Given `c : Fin n → ℂ`, `r : Fin n → ℝ` with `0 < r k` for all `k`, and `g : (Fin n → ℂ) → ℂ` of class `C¹` with `g z = 0` whenever some coordinate satisfies `r k / 2 ≤ ‖z k - c k‖`, there is `M : ℝ` with `‖fderiv ℝ g z‖ ≤ M` for every `z`.
Indeed `fderiv ℝ g` vanishes at every `z` with some `r k / 2 < ‖z k - c k‖` (there `g` is `0` on a whole neighbourhood, so `g` is locally constant), so `fderiv ℝ g` is supported in the compact closed polydisc `{z | ∀ k, ‖z k - c k‖ ≤ r k / 2}`; being continuous, its norm is bounded there (`IsCompact.exists_isMaxOn`, or closed-and-bounded in the finite dimensional space `Fin n → ℂ`), and it is `0` outside. -/
theorem exists_norm_fderiv_le_of_halfPolydisc_support {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j) {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ z : Fin n → ℂ, (∃ k, r k / 2 ≤ ‖z k - c k‖) → g z = 0) :
    ∃ M : ℝ, ∀ z : Fin n → ℂ, ‖fderiv ℝ g z‖ ≤ M := by
  classical
  -- the norm of the differential is continuous
  have hfg : Continuous (fun z : Fin n → ℂ => ‖fderiv ℝ g z‖) :=
    (hg.continuous_fderiv (by norm_num)).norm
  -- the differential vanishes strictly inside the complement of the closed half polydisc
  have hzero : ∀ z : Fin n → ℂ, (∃ k, r k / 2 < ‖z k - c k‖) → fderiv ℝ g z = 0 := by
    intro z hzk
    obtain ⟨k, hk⟩ := hzk
    have hε : 0 < ‖z k - c k‖ - r k / 2 := by linarith
    have hev : g =ᶠ[nhds z] (fun _ : Fin n → ℂ => (0 : ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds z hε] with w hw
      rw [Metric.mem_ball] at hw
      refine hsupp w ⟨k, ?_⟩
      have h1 : ‖w k - z k‖ ≤ ‖w - z‖ := norm_le_pi_norm (w - z) k
      have h2 : ‖w - z‖ < ‖z k - c k‖ - r k / 2 := by
        rw [← dist_eq_norm]; exact hw
      have h3 : ‖z k - c k‖ ≤ ‖z k - w k‖ + ‖w k - c k‖ := by
        have h := dist_triangle (z k) (w k) (c k)
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h
        exact h
      have h4 : ‖z k - w k‖ = ‖w k - z k‖ := norm_sub_rev _ _
      linarith
    rw [hev.fderiv_eq]
    simp
  -- the closed half polydisc
  set K : Set (Fin n → ℂ) := {z | ∀ k, ‖z k - c k‖ ≤ r k / 2} with hK
  have hKclosed : IsClosed K := by
    have h : K = ⋂ k, {z : Fin n → ℂ | ‖z k - c k‖ ≤ r k / 2} := by
      ext z; simp [hK, Set.mem_iInter]
    rw [h]
    refine isClosed_iInter fun k => isClosed_le ?_ continuous_const
    exact ((continuous_apply k).sub continuous_const).norm
  have hnn : ∀ i, 0 ≤ r i / 2 := fun i => div_nonneg (le_of_lt (hr i)) (by norm_num)
  have hsum_nn : 0 ≤ ∑ k, r k / 2 := Finset.sum_nonneg fun i _ => hnn i
  have hKsub : K ⊆ Metric.closedBall c (∑ k, r k / 2) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [pi_norm_le_iff_of_nonneg hsum_nn]
    intro k
    have h1 := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hnn i) (Finset.mem_univ k)
    exact (hz k).trans h1
  have hKcompact : IsCompact K :=
    (isCompact_closedBall c (∑ k, r k / 2)).of_isClosed_subset hKclosed hKsub
  have hKne : K.Nonempty := ⟨c, fun k => by
    rw [sub_self, norm_zero]
    exact hnn k⟩
  -- the norm of the differential attains its maximum on `K`
  obtain ⟨z₀, _, hz₀max⟩ := hKcompact.exists_isMaxOn hKne hfg.continuousOn
  refine ⟨‖fderiv ℝ g z₀‖, fun z => ?_⟩
  by_cases hz : z ∈ K
  · exact hz₀max hz
  · have hz' : ∃ k, r k / 2 < ‖z k - c k‖ := by
      rw [hK] at hz
      simp only [Set.mem_ofPred_eq, not_forall] at hz
      obtain ⟨k, hk⟩ := hz
      exact ⟨k, not_le.mp hk⟩
    rw [hzero z hz']
    simp

end Work.CR.Flat.Cauchy
