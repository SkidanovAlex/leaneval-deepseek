import Mathlib

namespace Work.ZeroFreeTables.P9

open scoped BigOperators

/-!
# A uniform bound for the trivial series `∑ ‖(1/(s + a + 2n))^k‖`

For `Re s ≥ 1/2`, `a : ℕ` and `k ≥ 2` the series `∑_n ‖(1 / (s + (a + 2n)))^k‖`
is bounded by the constant `2^k * 2`.  The only analytic input is the `p`-series
bound `∑_n 1/(n+1)^k ≤ 2` for `k ≥ 2`, proved here by an elementary telescoping
comparison (no zeta values needed).
-/

/-- Pointwise telescoping comparison: `1/(i+1)^k ≤ 2 (1/(i+1) - 1/(i+2))` for `k ≥ 2`. -/
private lemma one_div_succ_pow_le (k : ℕ) (hk : 2 ≤ k) (i : ℕ) :
    (1 : ℝ) / ((i : ℝ) + 1) ^ k ≤ 2 * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
  have hx : (1 : ℝ) ≤ (i : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  have h1 : (1 : ℝ) / ((i : ℝ) + 1) ^ k ≤ 1 / ((i : ℝ) + 1) ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ hx hk
  have h2 : (1 : ℝ) / ((i : ℝ) + 1) ^ 2 ≤ 2 * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
    field_simp
    nlinarith
  exact h1.trans h2

/-- Telescoping value of `∑_{i<N} (1/(i+1) - 1/(i+2))`. -/
private lemma sum_range_telescope (N : ℕ) :
    (∑ i ∈ Finset.range N, ((1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)))
      = 1 - 1 / ((N : ℝ) + 1) := by
  calc (∑ i ∈ Finset.range N, ((1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)))
      = ∑ i ∈ Finset.range N,
          ((-(1 / (((i + 1 : ℕ) : ℝ) + 1))) - (-(1 / (((i : ℕ) : ℝ) + 1)))) := by
          apply Finset.sum_congr rfl; intro i _; push_cast; ring
    _ = (-(1 / (((N : ℕ) : ℝ) + 1))) - (-(1 / (((0 : ℕ) : ℝ) + 1))) :=
          Finset.sum_range_sub (fun i : ℕ => -(1 / (((i : ℕ) : ℝ) + 1))) N
    _ = 1 - 1 / ((N : ℝ) + 1) := by push_cast; ring

/-- Partial-sum bound for the `p`-series `∑ 1/(i+1)^k`, `k ≥ 2`. -/
private lemma sum_range_inv_pow_le (k : ℕ) (hk : 2 ≤ k) (N : ℕ) :
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) ^ k) ≤ 2 := by
  have htel := sum_range_telescope N
  calc (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) ^ k)
      ≤ ∑ i ∈ Finset.range N, 2 * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) :=
          Finset.sum_le_sum (fun i _ => one_div_succ_pow_le k hk i)
    _ = 2 * ∑ i ∈ Finset.range N, ((1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
          rw [Finset.mul_sum]
    _ = 2 * (1 - 1 / ((N : ℝ) + 1)) := by rw [htel]
    _ ≤ 2 := by
          have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
          linarith

/-- The `p`-series bound `∑_n 1/(n+1)^k ≤ 2` for `k ≥ 2`. -/
private lemma tsum_inv_pow_succ_le_two (k : ℕ) (hk : 2 ≤ k) :
    (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ k) ≤ 2 :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun N => sum_range_inv_pow_le k hk N)

/-- Summability of `∑_n 1/(n+1)^k` for `k ≥ 2`. -/
private lemma summable_inv_succ_pow (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ k) := by
  have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) :=
    (Real.summable_one_div_nat_pow (p := k)).mpr (by omega)
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ k) :=
    (summable_nat_add_iff 1).mpr h0
  exact h1.congr (fun n => by push_cast; ring)

/-- Pointwise norm bound: `‖(1/(s + (a + 2n)))^k‖ ≤ 2^k / (n+1)^k` when `Re s ≥ 1/2`. -/
private lemma norm_inv_pow_bound (s : ℂ) (hs : (1 : ℝ) / 2 ≤ s.re) (a n k : ℕ) :
    ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖ ≤ (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k := by
  set z : ℂ := s + ((a + 2 * n : ℕ) : ℂ) with hzdef
  have h1 : ((n : ℝ) + 1) / 2 ≤ ‖z‖ := by
    have h1' : z.re = s.re + ((a + 2 * n : ℕ) : ℝ) := by
      rw [hzdef, Complex.add_re, Complex.natCast_re]
    have h2 : ((a + 2 * n : ℕ) : ℝ) = (a : ℝ) + 2 * (n : ℝ) := by push_cast; ring
    have h3re : ((n : ℝ) + 1) / 2 ≤ z.re := by
      rw [h1', h2]
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      nlinarith [hs]
    calc ((n : ℝ) + 1) / 2 ≤ z.re := h3re
      _ ≤ ‖z‖ := Complex.re_le_norm _
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hpos h1
  have hle : ‖z‖⁻¹ ≤ 2 / ((n : ℝ) + 1) := by
    rw [show (2 : ℝ) / ((n : ℝ) + 1) = (((n : ℝ) + 1) / 2)⁻¹ by field_simp]
    exact (inv_le_inv₀ hzpos hpos).mpr h1
  have hnorm : ‖(1 / z) ^ k‖ = (‖z‖⁻¹) ^ k := by
    rw [show (1 : ℂ) / z = z⁻¹ by simp, norm_pow, norm_inv]
  rw [hnorm, show (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k = (2 / ((n : ℝ) + 1)) ^ k by rw [div_pow]]
  exact pow_le_pow_left₀ (by positivity) hle k

/-- Bound for the series of `k`-th powers, `k ≥ 2`. -/
private lemma tsum_norm_le (k : ℕ) (hk : 2 ≤ k) (s : ℂ) (hs : (1 : ℝ) / 2 ≤ s.re) (a : ℕ) :
    (∑' n : ℕ, ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖) ≤ (2 : ℝ) ^ k * 2 := by
  have hbase := summable_inv_succ_pow k hk
  have hmaj : Summable (fun n : ℕ => (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k) :=
    (hbase.mul_left ((2 : ℝ) ^ k)).congr (fun n => by rw [mul_one_div])
  have hnorm_summ : Summable (fun n : ℕ => ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_inv_pow_bound s hs a n k) hmaj
  calc (∑' n : ℕ, ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖)
      ≤ ∑' n : ℕ, (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k :=
          Summable.tsum_le_tsum (fun n => norm_inv_pow_bound s hs a n k) hnorm_summ hmaj
    _ = (2 : ℝ) ^ k * ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ k := by
          rw [← tsum_mul_left]; apply tsum_congr; intro n; rw [mul_one_div]
    _ ≤ (2 : ℝ) ^ k * 2 := by
          apply mul_le_mul_of_nonneg_left (tsum_inv_pow_succ_le_two k hk)
          positivity

theorem trivSeriesBound :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → ∀ a : ℕ, a ≤ 1 →
      (∑' n : ℕ, ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ 2‖) ≤ Ct ∧
      (∑' n : ℕ, ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ 3‖) ≤ Ct := by
  refine ⟨100, by norm_num, ?_⟩
  intro s hs a _ha
  constructor
  · have h := tsum_norm_le 2 (by norm_num) s hs a
    have h8 : (2 : ℝ) ^ 2 * 2 = 8 := by norm_num
    linarith
  · have h := tsum_norm_le 3 (by norm_num) s hs a
    have h16 : (2 : ℝ) ^ 3 * 2 = 16 := by norm_num
    linarith

end Work.ZeroFreeTables.P9
