import Mathlib

namespace Work.A3

/-- Elementary bracket estimate for the major-gap case: if `1 ≤ x ≤ N^{d/2}` and `N^η < x` with
`0 < η ≤ 1`, then
`(x⁻¹ + N⁻¹ + x·N^{-d})^p ≤ 3^p · N^{-ηp}` where `p = 2^{-(d-1)}`.

Indeed `x⁻¹ ≤ N^{-η}`, `N⁻¹ ≤ N^{-η}` and `x·N^{-d} ≤ N^{-d/2} ≤ N^{-η}`, so the bracket is at
most `3 N^{-η}`; both sides are nonnegative and `p > 0`. -/
theorem bracket_le_of_majorGap {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx1 : 1 ≤ x)
    (hx2 : x ≤ (N : ℝ) ^ ((d : ℝ) / 2)) (hx3 : (N : ℝ) ^ η < x) :
    (x⁻¹ + (N : ℝ)⁻¹ + x * (N : ℝ) ^ (-(d : ℤ))) ^ ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) ≤
      (3 : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) *
        (N : ℝ) ^ (-(η * ((1 : ℝ) / (2 : ℝ) ^ (d - 1)))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
  have hNηpos : 0 < (N : ℝ) ^ η := Real.rpow_pos_of_pos hNpos η
  have hNηle : (N : ℝ) ^ η ≤ x := le_of_lt hx3
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  -- integer and real exponents of `N` agree
  have hconv : (N : ℝ) ^ (-(d : ℤ)) = (N : ℝ) ^ (-(d : ℝ)) := by
    rw [← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  -- first term
  have t1 : x⁻¹ ≤ (N : ℝ) ^ (-η) := by
    have h := (inv_le_inv₀ hxpos hNηpos).mpr hNηle
    rwa [← Real.rpow_neg hNpos.le η] at h
  -- second term
  have t2 : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-η) := by
    have h := Real.rpow_le_rpow_of_exponent_le hNge1 (show (-1 : ℝ) ≤ -η by linarith)
    rwa [Real.rpow_neg_one] at h
  -- third term
  have t3 : x * (N : ℝ) ^ (-(d : ℤ)) ≤ (N : ℝ) ^ (-η) := by
    rw [hconv]
    calc x * (N : ℝ) ^ (-(d : ℝ))
        ≤ (N : ℝ) ^ ((d : ℝ) / 2) * (N : ℝ) ^ (-(d : ℝ)) :=
          mul_le_mul_of_nonneg_right hx2 (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ ((d : ℝ) / 2 + -(d : ℝ)) := (Real.rpow_add hNpos _ _).symm
      _ = (N : ℝ) ^ (-(d : ℝ) / 2) := by congr 1; ring
      _ ≤ (N : ℝ) ^ (-η) := Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
  -- the bracket is bounded by `3 N^{-η}`
  have hA : x⁻¹ + (N : ℝ)⁻¹ + x * (N : ℝ) ^ (-(d : ℤ)) ≤ 3 * (N : ℝ) ^ (-η) := by
    calc x⁻¹ + (N : ℝ)⁻¹ + x * (N : ℝ) ^ (-(d : ℤ))
        ≤ (N : ℝ) ^ (-η) + (N : ℝ) ^ (-η) + (N : ℝ) ^ (-η) :=
          add_le_add (add_le_add t1 t2) t3
      _ = 3 * (N : ℝ) ^ (-η) := by ring
  have hAnonneg : 0 ≤ x⁻¹ + (N : ℝ)⁻¹ + x * (N : ℝ) ^ (-(d : ℤ)) := by
    rw [hconv]
    have h1 : 0 ≤ x⁻¹ := inv_nonneg.mpr hxpos.le
    have h2 : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
    have h3 : 0 ≤ x * (N : ℝ) ^ (-(d : ℝ)) :=
      mul_nonneg hxpos.le (Real.rpow_nonneg hNpos.le _)
    linarith
  have hp : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ (d - 1) := by positivity
  calc (x⁻¹ + (N : ℝ)⁻¹ + x * (N : ℝ) ^ (-(d : ℤ))) ^ ((1 : ℝ) / (2 : ℝ) ^ (d - 1))
      ≤ (3 * (N : ℝ) ^ (-η)) ^ ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) :=
        Real.rpow_le_rpow hAnonneg hA hp
    _ = (3 : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) *
          ((N : ℝ) ^ (-η)) ^ ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) :=
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNpos.le _)
    _ = (3 : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) *
          (N : ℝ) ^ (-(η * ((1 : ℝ) / (2 : ℝ) ^ (d - 1)))) := by
        rw [← Real.rpow_mul hNpos.le]
        rw [show (-η) * ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) =
            -(η * ((1 : ℝ) / (2 : ℝ) ^ (d - 1))) by ring]

end Work.A3
