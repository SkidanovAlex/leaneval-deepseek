import Mathlib
import Submission.Work.ZeroFreeTables.P9.trivSeriesBound

namespace Work.ZeroFreeTables.P9

open scoped BigOperators

/-!
# Uniform bounds for the real parts of the parity series `∑ (1/(s+a+2n))^k`

For `Re s ≥ 1/2`, `a : ℕ` and `k ≥ 2` the series of real parts
`∑_n Re ((1 / (s + (a + 2n)))^k)` is absolutely bounded by the constant
`2^k * 2`.  The only analytic input is the elementary `p`-series bound
`∑_n 1/(n+1)^k ≤ 2` for `k ≥ 2` (proved by telescoping, no zeta values).
-/

/-- Pointwise telescoping comparison: `1/(i+1)^k ≤ 2 (1/(i+1) - 1/(i+2))` for `k ≥ 2`. -/
private lemma pb_one_div_succ_pow_le (k : ℕ) (hk : 2 ≤ k) (i : ℕ) :
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
private lemma pb_sum_range_telescope (N : ℕ) :
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
private lemma pb_sum_range_inv_pow_le (k : ℕ) (hk : 2 ≤ k) (N : ℕ) :
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) ^ k) ≤ 2 := by
  have htel := pb_sum_range_telescope N
  calc (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) ^ k)
      ≤ ∑ i ∈ Finset.range N, 2 * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) :=
          Finset.sum_le_sum (fun i _ => pb_one_div_succ_pow_le k hk i)
    _ = 2 * ∑ i ∈ Finset.range N, ((1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
          rw [Finset.mul_sum]
    _ = 2 * (1 - 1 / ((N : ℝ) + 1)) := by rw [htel]
    _ ≤ 2 := by
          have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
          linarith

/-- The `p`-series bound `∑_n 1/(n+1)^k ≤ 2` for `k ≥ 2`. -/
private lemma pb_tsum_inv_pow_succ_le_two (k : ℕ) (hk : 2 ≤ k) :
    (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ k) ≤ 2 :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun N => pb_sum_range_inv_pow_le k hk N)

/-- Summability of `∑_n 1/(n+1)^k` for `k ≥ 2`. -/
private lemma pb_summable_inv_succ_pow (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ k) := by
  have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) :=
    (Real.summable_one_div_nat_pow (p := k)).mpr (by omega)
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ k) :=
    (summable_nat_add_iff 1).mpr h0
  exact h1.congr (fun n => by push_cast; ring)

/-- Pointwise bound: `|Re ((1/(s + (a + 2n)))^k)| ≤ 2^k / (n+1)^k` for `Re s ≥ 1/2`. -/
private lemma pb_re_abs_le (s : ℂ) (hs : (1 : ℝ) / 2 ≤ s.re) (a n k : ℕ) :
    |((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k).re| ≤ (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k := by
  set z : ℂ := s + ((a + 2 * n : ℕ) : ℂ) with hz
  have h1 : ((n : ℝ) + 1) / 2 ≤ ‖z‖ := by
    have h1' : z.re = s.re + ((a + 2 * n : ℕ) : ℝ) := by
      rw [hz, Complex.add_re, Complex.natCast_re]
    have h2 : ((a + 2 * n : ℕ) : ℝ) = (a : ℝ) + 2 * (n : ℝ) := by push_cast; ring
    have h3re : ((n : ℝ) + 1) / 2 ≤ z.re := by
      rw [h1', h2]
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      nlinarith [hs]
    linarith [h3re, Complex.re_le_norm z]
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hpos h1
  have hle1 : 1 / ‖z‖ ≤ 2 / ((n : ℝ) + 1) := by
    rw [one_div, show (2 : ℝ) / ((n : ℝ) + 1) = (((n : ℝ) + 1) / 2)⁻¹ by field_simp]
    exact (inv_le_inv₀ hzpos hpos).mpr h1
  have hnorm : ‖(1 / z) ^ k‖ = (1 / ‖z‖) ^ k := by
    rw [show (1 : ℂ) / z = z⁻¹ by simp, norm_pow, norm_inv, one_div]
  calc |((1 / z) ^ k).re| ≤ ‖(1 / z) ^ k‖ := Complex.abs_re_le_norm _
    _ = (1 / ‖z‖) ^ k := hnorm
    _ ≤ (2 / ((n : ℝ) + 1)) ^ k := pow_le_pow_left₀ (by positivity) hle1 k
    _ = (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k := by rw [div_pow]

/-- Series bound: `|∑_n Re ((1/(s + (a + 2n)))^k)| ≤ 2^k * 2` for `Re s ≥ 1/2`, `k ≥ 2`. -/
private lemma pb_tsum_re_abs_le (s : ℂ) (hs : (1 : ℝ) / 2 ≤ s.re) (a k : ℕ) (hk : 2 ≤ k) :
    |∑' n : ℕ, (((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re| ≤ (2 : ℝ) ^ k * 2 := by
  have hbase := pb_summable_inv_succ_pow k hk
  have hmaj : Summable (fun n : ℕ => (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k) :=
    (hbase.mul_left ((2 : ℝ) ^ k)).congr (fun n => by rw [mul_one_div])
  have hbound : ∀ n : ℕ,
      ‖(((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re‖ ≤ (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k := by
    intro n
    rw [Real.norm_eq_abs]
    exact pb_re_abs_le s hs a n k
  have hsummnorm : Summable (fun n : ℕ => ‖(((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hbound n) hmaj
  calc |∑' n : ℕ, (((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re|
      = ‖∑' n : ℕ, (((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, ‖(((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re‖ :=
          norm_tsum_le_tsum_norm hsummnorm
    _ ≤ ∑' n : ℕ, (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k :=
          Summable.tsum_le_tsum (fun n => hbound n) hsummnorm hmaj
    _ = (2 : ℝ) ^ k * ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ k := by
          rw [← tsum_mul_left]; apply tsum_congr; intro n; rw [mul_one_div]
    _ ≤ (2 : ℝ) ^ k * 2 := by
          apply mul_le_mul_of_nonneg_left (pb_tsum_inv_pow_succ_le_two k hk)
          positivity

theorem parity_bound_re :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → ∀ par : ℕ, par ≤ 2 →
      |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct ∧
      |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct := by
  refine ⟨100, by norm_num, ?_⟩
  intro s hs par _hpar
  constructor
  · have h := pb_tsum_re_abs_le s hs par 2 (by norm_num)
    have h8 : (2 : ℝ) ^ 2 * 2 = 8 := by norm_num
    linarith
  · have h := pb_tsum_re_abs_le s hs par 3 (by norm_num)
    have h16 : (2 : ℝ) ^ 3 * 2 = 16 := by norm_num
    linarith

end Work.ZeroFreeTables.P9
