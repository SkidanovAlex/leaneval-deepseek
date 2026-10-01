import Mathlib
import Submission.Work.LinnikAreas.RpowGeom.rpow_mul_pow_identity
import Submission.Work.LinnikAreas.RpowGeom.two_rpow_neg_half_le

namespace Work.LinnikAreas

/-- **Partial geometric sums.**  For `0 ≤ r < 1`, any finite sub-sum of the geometric
series `∑ r^j` is at most the full sum `(1-r)⁻¹`. -/
theorem geom_sum_finset_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : Finset ℕ) :
    ∑ j ∈ s, r^j ≤ (1 - r)⁻¹ := by
  have h1r : 0 < 1 - r := by linarith
  set N := s.sup id + 1 with hN
  have hsub : s ⊆ Finset.range N := by
    intro j hj
    rw [Finset.mem_range]
    have h1 : j ≤ s.sup id := Finset.le_sup (f := id) hj
    omega
  have hle : ∑ j ∈ s, r^j ≤ ∑ j ∈ Finset.range N, r^j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro x _ _
    exact pow_nonneg hr0 x
  have hgeom : ∑ j ∈ Finset.range N, r^j ≤ (1 - r)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ h1r]
    have hgm := geom_sum_mul r N
    have hpow : (0:ℝ) ≤ r^N := pow_nonneg hr0 N
    nlinarith
  linarith

/-- **The dyadic layer sum.**  For any finite set `J` of layer indices,
`Σ_{j∈J} (4^j)⁻¹(2^{j+1})^{3/2} ≤ 2^{3/2}·(1 - 2^{-1/2})⁻¹` (the layer terms collapse to
`2^{3/2}·(2^{-1/2})^j`, a geometric series of ratio `2^{-1/2} < 1`). -/
theorem dyadicGeomFree (J : Finset ℕ) :
    (∑ j ∈ J, ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ))
      ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := by
  set r : ℝ := (2 : ℝ) ^ (-(1 / 2) : ℝ) with hr
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hterm : ∀ j : ℕ,
      ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) * r^j := by
    intro j
    have h := RpowGeom.rpow_mul_pow_identity (1 : ℝ) one_pos (3 / 2 : ℝ) j
    simp only [one_mul, Real.one_rpow] at h
    have hexp : (3 / 2 : ℝ) - 2 = -(1 / 2 : ℝ) := by norm_num
    rw [hexp] at h
    rw [hr]
    exact h
  have hsum_eq : (∑ j ∈ J, ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ))
      = (2 : ℝ) ^ (3 / 2 : ℝ) * ∑ j ∈ J, r^j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hterm j)
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.rpow_nonneg h2pos.le _
  have hr1 : r < 1 := by rw [hr]; linarith [RpowGeom.two_rpow_neg_half_le]
  rw [hsum_eq]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg h2pos.le _)
  exact geom_sum_finset_le_inv hr0 hr1 J

end Work.LinnikAreas
