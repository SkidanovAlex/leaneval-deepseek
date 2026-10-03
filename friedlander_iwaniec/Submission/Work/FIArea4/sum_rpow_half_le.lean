import Mathlib

namespace Work.FIArea4

/-- Finite geometric-sum bound: for `0 ≤ r < 1` and any finite set `S` of naturals,
`∑_{j ∈ S} r^j ≤ (1 - r)⁻¹`.

Compare the finite sum with the full geometric series, whose value is `(1 - r)⁻¹`. -/
lemma sum_pow_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (S : Finset ℕ) :
    ∑ j ∈ S, r ^ j ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum S (fun i _ => pow_nonneg hr0 i)

/-- Shifted geometric-sum bound: if every `k ∈ S` satisfies `k0 ≤ k`, then
`∑_{k ∈ S} r^k ≤ r^{k0} · (1 - r)⁻¹`
for `0 ≤ r < 1`.  Each `r^k` is written as `r^{k0} · r^{k - k0}`, the factor `r^{k0}`
is pulled out, and the remaining exponents `k - k0` form a finite set of naturals
bounded by the full geometric series. -/
lemma sum_pow_shift_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {S : Finset ℕ} {k0 : ℕ}
    (h : ∀ k ∈ S, k0 ≤ k) :
    ∑ k ∈ S, r ^ k ≤ r ^ k0 * (1 - r)⁻¹ := by
  have hinj : Set.InjOn (fun k => k - k0) ↑S := by
    intro a ha b hb hab
    have h1 : k0 ≤ a := h a ha
    have h2 : k0 ≤ b := h b hb
    have hab' : a - k0 = b - k0 := hab
    omega
  have hshift : ∑ k ∈ S, r ^ (k - k0) = ∑ j ∈ S.image (fun k => k - k0), r ^ j :=
    (Finset.sum_image hinj).symm
  calc ∑ k ∈ S, r ^ k
      = ∑ k ∈ S, r ^ k0 * r ^ (k - k0) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← pow_add, Nat.add_sub_of_le (h k hk)]
    _ = r ^ k0 * ∑ k ∈ S, r ^ (k - k0) := by rw [Finset.mul_sum]
    _ = r ^ k0 * ∑ j ∈ S.image (fun k => k - k0), r ^ j := by rw [hshift]
    _ ≤ r ^ k0 * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left (sum_pow_le_inv_one_sub hr0 hr1 _) (pow_nonneg hr0 k0)

/-- For a finite set `T` of naturals all of which are `≥ k0`,
`∑_{k ∈ T} (2^k)^{-1/2} ≤ 4 · (2^{k0})^{-1/2}`.

Write `(2^k)^{-1/2} = (2^{-1/2})^k` (an instance of `(x a)^b = (x^b)^a` for `x = 2 > 0`),
so the sum is a truncated geometric series with ratio `r = 2^{-1/2} ∈ (0,1)`.  The shifted
bound `sum_pow_shift_le` gives `≤ r^{k0} (1 - r)⁻¹`, and `(1 - r)⁻¹ ≤ 4` because
`r = 1/√2 ≤ 3/4`, i.e. `4 ≤ 3√2`. -/
lemma sum_rpow_half_le {T : Finset ℕ} {k0 : ℕ} (hk0 : ∀ k ∈ T, k0 ≤ k) :
    (∑ k ∈ T, ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 2)) ≤ 4 * ((2 : ℝ) ^ k0) ^ (-(1 : ℝ) / 2) := by
  have hterm : ∀ k : ℕ, ((2:ℝ)^k) ^ (-(1:ℝ)/2) = ((2:ℝ)^(-(1:ℝ)/2))^k := by
    intro k
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    calc ((2:ℝ)^k) ^ (-(1:ℝ)/2)
        = ((2:ℝ)^(k:ℝ)) ^ (-(1:ℝ)/2) := by rw [Real.rpow_natCast]
      _ = (2:ℝ)^((k:ℝ) * (-(1:ℝ)/2)) := by rw [← Real.rpow_mul h2]
      _ = (2:ℝ)^((-(1:ℝ)/2) * (k:ℝ)) := by ring_nf
      _ = ((2:ℝ)^(-(1:ℝ)/2))^(k:ℝ) := by rw [Real.rpow_mul h2]
      _ = ((2:ℝ)^(-(1:ℝ)/2))^k := by rw [Real.rpow_natCast]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), hterm k0]
  set r : ℝ := (2:ℝ)^(-(1:ℝ)/2) with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr_sqrt : r = (Real.sqrt 2)⁻¹ := by
    rw [hr]
    rw [Real.rpow_div_two_eq_sqrt (x := 2) (-1) (by norm_num : (0:ℝ) ≤ 2), Real.rpow_neg_one]
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr1 : r < 1 := by
    rw [hr_sqrt]
    exact inv_lt_one_of_one_lt₀ (by rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)]; norm_num)
  have her : r ≤ 3/4 := by
    rw [hr_sqrt, inv_le_iff_one_le_mul₀ hs2]
    have h43 : (4:ℝ)/3 ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num : (0:ℝ) ≤ 4/3) (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    nlinarith [h43]
  have h4 : (1 - r)⁻¹ ≤ 4 := by
    have hpos : 0 < 1 - r := by linarith
    rw [inv_le_iff_one_le_mul₀ hpos]
    linarith
  calc ∑ k ∈ T, r^k ≤ r^k0 * (1-r)⁻¹ := sum_pow_shift_le hr0 hr1 hk0
    _ ≤ r^k0 * 4 := mul_le_mul_of_nonneg_left h4 (pow_nonneg hr0 k0)
    _ = 4 * r^k0 := by ring

end Work.FIArea4
