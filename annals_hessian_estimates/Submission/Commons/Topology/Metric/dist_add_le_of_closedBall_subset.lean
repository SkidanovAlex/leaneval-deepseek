import Mathlib.Analysis.Normed.Module.Basic

namespace Commons.Topology.Metric

theorem dist_add_le_of_closedBall_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {x y : E} {r R : ℝ} (hr : 0 ≤ r)
    (h : Metric.closedBall x r ⊆ Metric.closedBall y R) : dist x y + r ≤ R := by
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hdist : dist x (x + (r / ‖v‖) • v) = r := by
      rw [dist_eq_norm', add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hr hvpos.le), div_mul_cancel₀ _ hvpos.ne']
    have hmem : x + (r / ‖v‖) • v ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_comm, hdist]
    have h1 : dist (x + (r / ‖v‖) • v) x ≤ R := Metric.mem_closedBall.mp (h hmem)
    rw [dist_comm, hdist] at h1
    simpa using h1
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hdy : 0 < ‖x - y‖ := by rwa [dist_eq_norm] at hd
    have hdist : dist x (x + (r / dist x y) • (x - y)) = r := by
      rw [dist_eq_norm', add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hr hd.le), dist_eq_norm, div_mul_cancel₀ _ hdy.ne']
    have hmem : x + (r / dist x y) • (x - y) ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_comm, hdist]
    have h1 : dist (x + (r / dist x y) • (x - y)) y ≤ R := Metric.mem_closedBall.mp (h hmem)
    have hdist2 : dist (x + (r / dist x y) • (x - y)) y = dist x y + r := by
      have hsplit : x + (r / dist x y) • (x - y) - y = (1 + r / dist x y) • (x - y) := by
        rw [add_smul, one_smul]
        abel
      rw [dist_eq_norm, hsplit, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + r / dist x y), ← dist_eq_norm,
        add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hd)]
    linarith [h1, hdist2]

end Commons.Topology.Metric