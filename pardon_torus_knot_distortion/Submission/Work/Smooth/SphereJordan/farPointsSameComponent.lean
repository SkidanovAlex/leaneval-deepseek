import Mathlib

namespace Work.Smooth.SphereJordan

/-- Points far from the origin all lie in the same connected component of the complement of a
finite union of closed balls contained in a disk of radius `M`. -/
theorem farPointsSameComponent (P : Finset ℂ) {r M : ℝ} (hr : 0 < r)
    (hM : ∀ w ∈ P, ‖w‖ + r < M) {z z' : ℂ} (hz : M < ‖z‖) (hz' : M < ‖z'‖) :
    z' ∈ connectedComponentIn (⋃ w ∈ P, Metric.closedBall w r)ᶜ z := by
  have _hr : (0 : ℝ) < r := hr
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hsphere : IsConnected (Metric.sphere (0 : ℂ) (1 : ℝ)) :=
    isConnected_sphere hrank (0 : ℂ) (r := 1) (by norm_num)
  -- The set `{x | M < ‖x‖}` is the image of the connected set `(M,∞) × S¹` under scalar
  -- multiplication, hence connected.
  have hEq : (fun p : ℝ × ℂ => p.1 • p.2) '' (Set.Ioi M ×ˢ Metric.sphere (0 : ℂ) (1 : ℝ))
      = {x : ℂ | M < ‖x‖} := by
    ext x
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      change M < ‖t • u‖
      have ht1 : M < t := by simpa using ht
      have hu1 : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hu
      rw [norm_smul, Real.norm_eq_abs, hu1, mul_one]
      exact lt_of_lt_of_le ht1 (le_abs_self t)
    · intro hx
      change M < ‖x‖ at hx
      rcases eq_or_ne ‖x‖ 0 with h0 | h0
      · refine ⟨(0, (1 : ℂ)), ⟨?_, ?_⟩, ?_⟩
        · rw [Set.mem_Ioi]; rw [h0] at hx; exact hx
        · simp
        · show (0 : ℝ) • (1 : ℂ) = x
          rw [zero_smul, norm_eq_zero.mp h0]
      · refine ⟨(‖x‖, (‖x‖)⁻¹ • x), ⟨?_, ?_⟩, ?_⟩
        · exact hx
        · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ h0]
        · show ‖x‖ • ((‖x‖)⁻¹ • x) = x
          rw [← mul_smul, mul_inv_cancel₀ h0, one_smul]
  have hconn : IsConnected {x : ℂ | M < ‖x‖} := by
    rw [← hEq]
    exact IsConnected.image (isConnected_Ioi.prod hsphere)
      (fun p : ℝ × ℂ => p.1 • p.2) (continuous_fst.smul continuous_snd).continuousOn
  -- `{x | M < ‖x‖}` avoids every ball of the union.
  have hsub : {x : ℂ | M < ‖x‖} ⊆ (⋃ w ∈ P, Metric.closedBall w r)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    intro h
    have h1 : ‖w‖ + r < ‖x‖ := lt_trans (hM w hw) hx
    have h2 : ‖x‖ - ‖w‖ ≤ ‖x - w‖ := norm_sub_norm_le x w
    linarith
  exact IsPreconnected.subset_connectedComponentIn hconn.isPreconnected hz hsub hz'

end Work.Smooth.SphereJordan
