import Submission.Work.Deep.Sparse.Prelude
namespace Work.Deep.Sparse

/-- Elementary numeric bound used in the proof of `pt_hbig`: `ln 10 ≤ 3`. -/
lemma pt_hbig_log_ten_le_three : Real.log (10 : ℝ) ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h3 : Real.exp (3 : ℝ) = Real.exp 1 ^ (3 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  have h2 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ (3 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
  have h1 : (10 : ℝ) < (2.7182818283 : ℝ) ^ 3 := by norm_num
  linarith

/-- The core transcendental inequality of `pt_hbig`: if `u ≥ 10^24` then
`10^6 * ((4/3) * log u)^8 ≤ u`.  Writing `w = log u ≥ 24 log 10` and
`s = w - 24 log 10 ≥ 0`, we have `exp (w/8) = 1000 * exp (s/8) ≥ 1000 * (1 + s/8)`,
while `8 w = 192 log 10 + 8 s ≤ 576 + 8 s`, so `8w ≤ exp (w/8)`; raising to the
eighth power and using `10^6 * (4/3)^8 ≤ 8^8` gives the claim. -/
lemma pt_hbig_core {u : ℝ} (hu : (10 : ℝ) ^ 24 ≤ u) :
    (10 : ℝ) ^ 6 * ((4 / 3) * Real.log u) ^ 8 ≤ u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (by norm_num) hu
  have hlog10nn : 0 ≤ Real.log (10 : ℝ) := Real.log_nonneg (by norm_num)
  have hw24 : 24 * Real.log (10 : ℝ) ≤ Real.log u := by
    have h := Real.log_le_log (show (0 : ℝ) < (10 : ℝ) ^ 24 by norm_num) hu
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hw0 : 0 ≤ Real.log u := by linarith
  have hexp : 8 * Real.log u ≤ Real.exp (Real.log u / 8) := by
    have hs : 0 ≤ Real.log u - 24 * Real.log (10 : ℝ) := by linarith
    have h1000 : Real.exp (3 * Real.log (10 : ℝ)) = 1000 := by
      rw [show (3 : ℝ) * Real.log 10 = Real.log ((10 : ℝ) ^ 3) by
            rw [Real.log_pow]; norm_num]
      rw [Real.exp_log (show (0 : ℝ) < (10 : ℝ) ^ 3 by norm_num)]
      norm_num
    have hsplit : Real.exp (Real.log u / 8)
        = 1000 * Real.exp ((Real.log u - 24 * Real.log (10 : ℝ)) / 8) := by
      rw [show Real.log u / 8
            = 3 * Real.log (10 : ℝ) + (Real.log u - 24 * Real.log (10 : ℝ)) / 8 by ring]
      rw [Real.exp_add, h1000]
    have hle1 : 1000 * ((Real.log u - 24 * Real.log (10 : ℝ)) / 8 + 1)
        ≤ Real.exp (Real.log u / 8) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by norm_num)
    have harith : 8 * Real.log u
        ≤ 1000 * ((Real.log u - 24 * Real.log (10 : ℝ)) / 8 + 1) := by
      nlinarith [hw24, pt_hbig_log_ten_le_three]
    linarith
  calc (10 : ℝ) ^ 6 * ((4 / 3) * Real.log u) ^ 8
      = (10 : ℝ) ^ 6 * ((4 / 3) ^ 8 * (Real.log u) ^ 8) := by rw [mul_pow]
    _ = ((10 : ℝ) ^ 6 * (4 / 3) ^ 8) * (Real.log u) ^ 8 := by ring
    _ ≤ 8 ^ 8 * (Real.log u) ^ 8 := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hw0 8)
    _ = (8 * Real.log u) ^ 8 := by rw [mul_pow]
    _ ≤ (Real.exp (Real.log u / 8)) ^ 8 := by
        exact pow_le_pow_left₀ (by positivity) hexp 8
    _ = Real.exp (Real.log u) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ = u := Real.exp_log hu0

/-- The largeness hypothesis propagates to the product `δ^2 * D`: from
`10^24 / δ^8 ≤ D` and `0 < δ ≤ 1` we get `10^24 ≤ δ^2 * D`. -/
lemma pt_hbig_u_ge {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : (10 : ℝ) ^ 24 / δ ^ 8 ≤ D) : (10 : ℝ) ^ 24 ≤ δ ^ 2 * D := by
  have hδ8pos : 0 < δ ^ 8 := pow_pos hδ0 8
  have hδ8le : δ ^ 8 ≤ 1 := pow_le_one₀ (le_of_lt hδ0) hδ1
  have hδ6pos : 0 < δ ^ 6 := pow_pos hδ0 6
  have hδ6le : δ ^ 6 ≤ 1 := pow_le_one₀ (le_of_lt hδ0) hδ1
  have hmain : δ ^ 2 * ((10 : ℝ) ^ 24 / δ ^ 8) = (10 : ℝ) ^ 24 / δ ^ 6 := by
    field_simp
  have h2 : (10 : ℝ) ^ 24 ≤ (10 : ℝ) ^ 24 / δ ^ 6 := by
    rw [le_div_iff₀ hδ6pos]
    nlinarith [hδ6le, show (0 : ℝ) < (10 : ℝ) ^ 24 by norm_num]
  calc (10 : ℝ) ^ 24 ≤ δ ^ 2 * ((10 : ℝ) ^ 24 / δ ^ 8) := by
        rw [hmain]; exact h2
    _ ≤ δ ^ 2 * D := mul_le_mul_of_nonneg_left hD (by positivity)

/-- `log (D + 2) ≤ (4/3) log (δ^2 * D)` under the hypothesis `10^24 / δ^8 ≤ D`,
`0 < δ ≤ 1`.  Indeed `D + 2 ≤ 3D`, `log D = log (δ^2 D) - 2 log δ`, and
`1/δ^6 ≤ δ^2 D / 10^24` (which is `δ^8 D ≥ 10^24`) gives
`-2 log δ ≤ (1/3) (log (δ^2 D) - 24 log 10)`; the rest is `log 3 ≤ 8 log 10`. -/
lemma pt_hbig_log_le_aux {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : (10 : ℝ) ^ 24 / δ ^ 8 ≤ D) :
    Real.log (D + 2) ≤ (4 / 3) * Real.log (δ ^ 2 * D) := by
  have hδ8pos : 0 < δ ^ 8 := pow_pos hδ0 8
  have hδ8le : δ ^ 8 ≤ 1 := pow_le_one₀ (le_of_lt hδ0) hδ1
  have hD24 : (10 : ℝ) ^ 24 ≤ D := by
    have h1 : (10 : ℝ) ^ 24 ≤ (10 : ℝ) ^ 24 / δ ^ 8 := by
      rw [le_div_iff₀ hδ8pos]
      nlinarith [hδ8le, show (0 : ℝ) < (10 : ℝ) ^ 24 by norm_num]
    linarith
  have hDpos : 0 < D := by linarith
  have hA : Real.log (D + 2) ≤ Real.log (3 * D) :=
    Real.log_le_log (by linarith) (by linarith)
  have hB : Real.log (3 * D) = Real.log 3 + Real.log D :=
    Real.log_mul (by norm_num) (ne_of_gt hDpos)
  have hC : Real.log D = Real.log (δ ^ 2 * D) - 2 * Real.log δ := by
    have h := Real.log_mul (ne_of_gt (pow_pos hδ0 2)) (ne_of_gt hDpos)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hδ8D : (10 : ℝ) ^ 24 ≤ δ ^ 8 * D := by
    have h := (div_le_iff₀ hδ8pos).mp hD
    nlinarith [h]
  have hle : 1 / δ ^ 6 ≤ (δ ^ 2 * D) / (10 : ℝ) ^ 24 := by
    rw [le_div_iff₀ (show (0 : ℝ) < (10 : ℝ) ^ 24 by norm_num),
        show 1 / δ ^ 6 * (10 : ℝ) ^ 24 = (10 : ℝ) ^ 24 / δ ^ 6 by ring,
        div_le_iff₀ (pow_pos hδ0 6),
        show (δ ^ 2 * D) * δ ^ 6 = δ ^ 8 * D by ring]
    exact hδ8D
  have hE : Real.log (1 / δ ^ 6) ≤ Real.log ((δ ^ 2 * D) / (10 : ℝ) ^ 24) :=
    Real.log_le_log (by positivity) hle
  have hE' : -6 * Real.log δ ≤ Real.log (δ ^ 2 * D) - 24 * Real.log (10 : ℝ) := by
    have h1 : Real.log (1 / δ ^ 6) = -6 * Real.log δ := by
      rw [Real.log_div (by norm_num) (ne_of_gt (pow_pos hδ0 6)), Real.log_pow]
      simp
    have h2 : Real.log ((δ ^ 2 * D) / (10 : ℝ) ^ 24)
        = Real.log (δ ^ 2 * D) - 24 * Real.log (10 : ℝ) := by
      rw [Real.log_div (ne_of_gt (mul_pos (pow_pos hδ0 2) hDpos)) (by norm_num),
          Real.log_pow]
      simp
    linarith [hE, h1, h2]
  have hlog3 : Real.log 3 ≤ 8 * Real.log (10 : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) ≤ (10 : ℝ) ^ 8)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  linarith [hA, hB, hC, hE', hlog3]

/-- The largeness condition of the naive-colouring-procedure concentration bound holds
whenever `D` is above the polynomial threshold `10^24 / δ^8` (with `0 < δ ≤ 1`). -/
theorem pt_hbig {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hD : (10 : ℝ) ^ 24 / δ ^ 8 ≤ D) :
    (10 : ℝ) ^ 6 * (Real.log (D + 2)) ^ 8 ≤ δ ^ 2 * D := by
  have hu : (10 : ℝ) ^ 24 ≤ δ ^ 2 * D := pt_hbig_u_ge hδ0 hδ1 hD
  have hlog : Real.log (D + 2) ≤ (4 / 3) * Real.log (δ ^ 2 * D) :=
    pt_hbig_log_le_aux hδ0 hδ1 hD
  have hδ8pos : 0 < δ ^ 8 := pow_pos hδ0 8
  have hδ8le : δ ^ 8 ≤ 1 := pow_le_one₀ (le_of_lt hδ0) hδ1
  have hD24 : (10 : ℝ) ^ 24 ≤ D := by
    have h1 : (10 : ℝ) ^ 24 ≤ (10 : ℝ) ^ 24 / δ ^ 8 := by
      rw [le_div_iff₀ hδ8pos]
      nlinarith [hδ8le, show (0 : ℝ) < (10 : ℝ) ^ 24 by norm_num]
    linarith
  have hlogpos : 0 ≤ Real.log (D + 2) := Real.log_nonneg (by linarith)
  calc (10 : ℝ) ^ 6 * (Real.log (D + 2)) ^ 8
      ≤ (10 : ℝ) ^ 6 * ((4 / 3) * Real.log (δ ^ 2 * D)) ^ 8 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogpos hlog 8) (by norm_num)
    _ ≤ δ ^ 2 * D := pt_hbig_core hu

end Work.Deep.Sparse
