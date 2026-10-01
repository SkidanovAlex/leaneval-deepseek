import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.tsum_inv_add_two_shift

namespace Work.ZeroFreeTables.Table4

open scoped BigOperators

/-!
# Uniform bounds for the "trivial" series `∑_n (1/(s + a + 2n))^k`

For `Re s ≥ 1`, `a : ℕ` and `k ≥ 2`, the series `∑_n ‖(1/(s + (a + 2n)))^k‖` is bounded
by `2`, hence so is the absolute value of the real part.  The analytic input is the
elementary `p`-series bound `∑_n 1/(n+1)^k ≤ 2` for `k ≥ 2`, proved by a telescoping
comparison.
-/

/-- Telescoping comparison: `1/(i+1)^k ≤ 2 (1/(i+1) - 1/(i+2))` for `k ≥ 2`. -/
private lemma triv_one_div_succ_pow_le (k : ℕ) (hk : 2 ≤ k) (i : ℕ) :
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
private lemma triv_sum_range_telescope (N : ℕ) :
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
private lemma triv_sum_range_inv_pow_le (k : ℕ) (hk : 2 ≤ k) (N : ℕ) :
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) ^ k) ≤ 2 := by
  have htel := triv_sum_range_telescope N
  calc (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) ^ k)
      ≤ ∑ i ∈ Finset.range N, 2 * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) :=
          Finset.sum_le_sum (fun i _ => triv_one_div_succ_pow_le k hk i)
    _ = 2 * ∑ i ∈ Finset.range N, ((1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
          rw [Finset.mul_sum]
    _ = 2 * (1 - 1 / ((N : ℝ) + 1)) := by rw [htel]
    _ ≤ 2 := by
          have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
          linarith

/-- The `p`-series bound `∑_n 1/(n+1)^k ≤ 2` for `k ≥ 2`. -/
private lemma triv_tsum_inv_pow_succ_le_two (k : ℕ) (hk : 2 ≤ k) :
    (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ k) ≤ 2 :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun N => triv_sum_range_inv_pow_le k hk N)

/-- Summability of `∑_n 1/(n+1)^k` for `k ≥ 2`. -/
private lemma triv_summable_inv_succ_pow (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ k) := by
  have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) :=
    (Real.summable_one_div_nat_pow (p := k)).mpr (by omega)
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ k) :=
    (summable_nat_add_iff 1).mpr h0
  exact h1.congr (fun n => by push_cast; ring)

/-- Pointwise norm bound: `‖(1/(s + (a + 2n)))^k‖ ≤ 1/(n+1)^k` when `Re s ≥ 1`. -/
private lemma triv_norm_term_bound (s : ℂ) (hs : 1 ≤ s.re) (a k n : ℕ) :
    ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) ^ k := by
  set z : ℂ := s + ((a + 2 * n : ℕ) : ℂ) with hzdef
  have hzre1 : z.re = s.re + ((a + 2 * n : ℕ) : ℝ) := by
    rw [hzdef, Complex.add_re, Complex.natCast_re]
  have hzre2 : ((a + 2 * n : ℕ) : ℝ) = (a : ℝ) + 2 * (n : ℝ) := by push_cast; ring
  have hzre3 : (n : ℝ) + 1 ≤ z.re := by
    rw [hzre1, hzre2]
    have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    linarith
  have hnorm : (n : ℝ) + 1 ≤ ‖z‖ := hzre3.trans (Complex.re_le_norm z)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : 1 / ‖z‖ ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le hpos hnorm
  calc ‖(1 / z) ^ k‖ = (1 / ‖z‖) ^ k := by rw [norm_pow, norm_div, norm_one]
    _ ≤ (1 / ((n : ℝ) + 1)) ^ k := pow_le_pow_left₀ (by positivity) hle k
    _ = (1 : ℝ) / ((n : ℝ) + 1) ^ k := by rw [div_pow, one_pow]

/-- Summability of the norm series `∑_n ‖(1/(s + (a + 2n)))^k‖` for `Re s ≥ 1`, `k ≥ 2`. -/
private lemma triv_summable_norm (s : ℂ) (hs : 1 ≤ s.re) (a k : ℕ) (hk : 2 ≤ k) :
    Summable (fun n : ℕ => ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => triv_norm_term_bound s hs a k n) (triv_summable_inv_succ_pow k hk)

/-- Bound for the norm series: `∑_n ‖(1/(s + (a + 2n)))^k‖ ≤ 2` for `Re s ≥ 1`, `k ≥ 2`. -/
private lemma triv_tsum_norm_le (s : ℂ) (hs : 1 ≤ s.re) (a k : ℕ) (hk : 2 ≤ k) :
    (∑' n : ℕ, ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖) ≤ 2 := by
  have hbase := triv_summable_inv_succ_pow k hk
  have hnorm := triv_summable_norm s hs a k hk
  exact (Summable.tsum_le_tsum (fun n => triv_norm_term_bound s hs a k n) hnorm hbase).trans
    (triv_tsum_inv_pow_succ_le_two k hk)

/-- Bound for the real part of the series, `|∑_n ((1/(s + (a + 2n)))^k).re| ≤ 2`. -/
private lemma triv_abs_re_tsum_le (s : ℂ) (hs : 1 ≤ s.re) (a k : ℕ) (hk : 2 ≤ k) :
    |∑' n : ℕ, (((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re| ≤ 2 := by
  have hnorm := triv_summable_norm s hs a k hk
  have hgs : Summable (fun n : ℕ => ‖(((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _) hnorm
  have hA : ‖∑' n : ℕ, (((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re‖ ≤
      ∑' n : ℕ, ‖(((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re‖ :=
    norm_tsum_le_tsum_norm hgs
  have hB : (∑' n : ℕ, ‖(((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re‖) ≤
      ∑' n : ℕ, ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖ :=
    Summable.tsum_le_tsum
      (fun n => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _) hgs hnorm
  calc |∑' n : ℕ, (((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re|
      = ‖∑' n : ℕ, (((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖(((1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k)).re‖ := hA
    _ ≤ ∑' n : ℕ, ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖ := hB
    _ ≤ 2 := triv_tsum_norm_le s hs a k hk

theorem trivSeries_le : ∃ Ct : ℝ, 0 < Ct ∧
    (∀ {s : ℂ} (hs : 1 ≤ s.re) (par : ℕ) (hpar : par ≤ 2),
      |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct ∧
      |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    ∧ (∀ {s : ℂ} (hs : 1 ≤ s.re),
      |∑' n : ℕ, (((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2)).re| ≤ Ct ∧
      |∑' n : ℕ, (((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3)).re| ≤ Ct) := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · intro s hs par _hpar
    exact ⟨triv_abs_re_tsum_le s hs par 2 (by norm_num),
           triv_abs_re_tsum_le s hs par 3 (by norm_num)⟩
  · intro s hs
    have h2 := triv_abs_re_tsum_le s hs 2 2 (by norm_num)
    have h3 := triv_abs_re_tsum_le s hs 2 3 (by norm_num)
    have key : ∀ n : ℕ, (2 * (n + 1) : ℕ) = (2 + 2 * n : ℕ) := fun n => by omega
    exact ⟨by simpa only [key] using h2, by simpa only [key] using h3⟩

end Work.ZeroFreeTables.Table4
