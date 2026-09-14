import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.Convex

open scoped Pointwise in
theorem smul_add_ball_subset_smul {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : Convex ℝ C) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ C)
    {r t₁ t₂ : ℝ} (hr : 0 ≤ r) (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ C) :
    (t₁ • C +ᵥ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ((t₂ - t₁) * r)) ⊆ t₂ • C := by
  intro z hz
  rcases (Set.mem_vadd.mp hz) with ⟨x, hx, y, hy, hzadd⟩
  rw [← hzadd]
  change x + y ∈ t₂ • C
  rcases (Set.mem_smul_set.mp hx) with ⟨c, hcC, hxeq⟩
  by_cases hd : t₂ - t₁ = 0
  · have hy0 : y = 0 := by
      have hy' : dist y 0 ≤ 0 := by
        simpa [hd] using (Metric.mem_closedBall.mp hy)
      exact dist_eq_zero.mp (le_antisymm hy' dist_nonneg)
    have h12 : t₁ = t₂ := by linarith
    rw [hy0, ← hxeq, h12]
    simpa using (Set.smul_mem_smul_set hcC)
  · have hdnonneg : 0 ≤ t₂ - t₁ := sub_nonneg.mpr ht
    have hdne0 : (0 : ℝ) ≠ t₂ - t₁ := fun h => hd h.symm
    have hdpos : 0 < t₂ - t₁ := lt_of_le_of_ne hdnonneg hdne0
    have ht₂pos : 0 < t₂ := by linarith
    let w : EuclideanSpace ℝ (Fin n) := ((t₂ - t₁)⁻¹) • y
    have hy_norm : ‖y‖ ≤ (t₂ - t₁) * r := by
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hy)
    have hw_norm : ‖w‖ ≤ r := by
      have hle : (t₂ - t₁)⁻¹ * ‖y‖ ≤ r := by
        calc
          (t₂ - t₁)⁻¹ * ‖y‖ ≤ (t₂ - t₁)⁻¹ * ((t₂ - t₁) * r) :=
            mul_le_mul_of_nonneg_left hy_norm (inv_nonneg.mpr hdnonneg)
          _ = r := by
            rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
      simpa [w, norm_smul_of_nonneg (inv_nonneg.mpr hdnonneg)] using hle
    have hwball : w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm] using hw_norm
    have hwC : w ∈ C := hball hwball
    let a : ℝ := (t₂ - t₁) / t₂
    let b : ℝ := t₁ / t₂
    have ha : 0 ≤ a := div_nonneg hdnonneg (le_of_lt ht₂pos)
    have hb : 0 ≤ b := div_nonneg ht₁ (le_of_lt ht₂pos)
    have hab : a + b = 1 := by
      dsimp [a, b]
      rw [← add_div]
      rw [show (t₂ - t₁) + t₁ = t₂ by ring]
      exact div_self (ne_of_gt ht₂pos)
    have hCcombo : a • w + b • c ∈ C := by
      exact (convex_iff_add_mem.mp hC) hwC hcC ha hb hab
    have hscalar_a : t₂ * a = t₂ - t₁ := by
      dsimp [a]
      field_simp [ne_of_gt ht₂pos]
    have hscalar_b : t₂ * b = t₁ := by
      dsimp [b]
      field_simp [ne_of_gt ht₂pos]
    have htw : (t₂ - t₁) • w = y := by
      dsimp [w]
      rw [smul_smul, mul_inv_cancel₀ hd, one_smul]
    have hmain : t₂ • (a • w + b • c) = x + y := by
      calc
        t₂ • (a • w + b • c) = (t₂ * a) • w + (t₂ * b) • c := by
          module
        _ = (t₂ - t₁) • w + t₁ • c := by
          rw [hscalar_a, hscalar_b]
        _ = y + t₁ • c := by
          rw [htw]
        _ = t₁ • c + y := by
          rw [add_comm]
        _ = x + y := by
          rw [hxeq]
    rw [Set.mem_smul_set]
    exact ⟨a • w + b • c, hCcombo, hmain⟩

end Commons.Analysis.Convex