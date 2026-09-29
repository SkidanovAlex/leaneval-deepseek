import Mathlib
import Submission.Work.Haupt.pentagonal_prelim

/-!
# The pentagonal "tail" sum tends to `0`

For `‖q‖ < 1` we show that

`k ↦ (-1)^{k+1} q^{(k+1)(3k+4)/2} ∑_{n≥0} q^{(k+1)n} ∏_{i=0}^{n} (1 - q^{k+i+1})`

tends to `0`.  The proof is a uniform estimate: writing `r = ‖q‖ < 1`, the partial
products `∏_{i=0}^{n}(1 - q^{k+i+1})` are uniformly bounded by `exp (r/(1-r))`
(lemma `norm_prod_range_one_sub_pow_le` of `pentagonal_prelim`), so the whole sum is
bounded by `exp (r/(1-r)) * (1-r)⁻¹` independently of `k`, while the prefactor is
dominated by `r^k → 0`.
-/

open scoped BigOperators
open Filter

namespace Work.Haupt

/-- Pointwise norm bound for a summand of the pentagonal tail sum. -/
private lemma penta_norm_prod_le (q : ℂ) (hq : ‖q‖ < 1) (k n : ℕ) :
    ‖q ^ ((k + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖
      ≤ Real.exp (‖q‖ / (1 - ‖q‖)) * ‖q‖ ^ n := by
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hE : 0 ≤ Real.exp (‖q‖ / (1 - ‖q‖)) := Real.exp_nonneg _
  have hp : ‖q‖ ^ ((k + 1) * n) ≤ ‖q‖ ^ n := by
    refine pow_le_pow_of_le_one hr0 hq.le ?_
    calc n = 1 * n := by ring
      _ ≤ (k + 1) * n := Nat.mul_le_mul_right n (by omega)
  calc ‖q ^ ((k + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖
      = ‖q‖ ^ ((k + 1) * n) * ‖∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖ := by
        rw [norm_mul, norm_pow]
    _ ≤ ‖q‖ ^ ((k + 1) * n) * Real.exp (‖q‖ / (1 - ‖q‖)) :=
        mul_le_mul_of_nonneg_left (norm_prod_range_one_sub_pow_le hq k n) (by positivity)
    _ ≤ ‖q‖ ^ n * Real.exp (‖q‖ / (1 - ‖q‖)) :=
        mul_le_mul_of_nonneg_right hp hE
    _ = Real.exp (‖q‖ / (1 - ‖q‖)) * ‖q‖ ^ n := by ring

/-- The pentagonal tail summand series is summable. -/
private lemma penta_summable (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Summable (fun n : ℕ => q ^ ((k + 1) * n) *
      ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => Real.exp (‖q‖ / (1 - ‖q‖)) * ‖q‖ ^ n) ?_ ?_
  · exact (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left _
  · intro n
    exact penta_norm_prod_le q hq k n

/-- Uniform bound on the pentagonal tail sum, valid for every `k`. -/
private lemma penta_tsum_norm_le (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    ‖∑' n : ℕ, q ^ ((k + 1) * n) *
        ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖
      ≤ Real.exp (‖q‖ / (1 - ‖q‖)) * (1 - ‖q‖)⁻¹ := by
  have hmaj : Summable (fun n : ℕ => Real.exp (‖q‖ / (1 - ‖q‖)) * ‖q‖ ^ n) :=
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left _
  have hsumm := penta_summable q hq k
  calc ‖∑' n : ℕ, q ^ ((k + 1) * n) *
          ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖
      ≤ ∑' n : ℕ, ‖q ^ ((k + 1) * n) *
          ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖ :=
        norm_tsum_le_tsum_norm hsumm.norm
    _ ≤ ∑' n : ℕ, Real.exp (‖q‖ / (1 - ‖q‖)) * ‖q‖ ^ n :=
        Summable.tsum_le_tsum (fun n => penta_norm_prod_le q hq k n) hsumm.norm hmaj
    _ = Real.exp (‖q‖ / (1 - ‖q‖)) * (1 - ‖q‖)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg q) hq]

/-- The full `k`-th pentagonal tail is bounded by `r^k` times a constant. -/
private lemma penta_tail_bound (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    ‖(-1 : ℂ) ^ (k + 1) * q ^ ((k + 1) * (3 * k + 4) / 2) *
      ∑' n : ℕ, q ^ ((k + 1) * n) *
        ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖
      ≤ ‖q‖ ^ k * (Real.exp (‖q‖ / (1 - ‖q‖)) * (1 - ‖q‖)⁻¹) := by
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hT := penta_tsum_norm_le q hq k
  have he : k ≤ (k + 1) * (3 * k + 4) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    nlinarith [Nat.zero_le k]
  have hpe : ‖q‖ ^ ((k + 1) * (3 * k + 4) / 2) ≤ ‖q‖ ^ k :=
    pow_le_pow_of_le_one hr0 hq.le he
  have hn : ‖(-1 : ℂ) ^ (k + 1) * q ^ ((k + 1) * (3 * k + 4) / 2) *
        (∑' n : ℕ, q ^ ((k + 1) * n) *
          ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1)))‖
      = ‖q‖ ^ ((k + 1) * (3 * k + 4) / 2) *
        ‖∑' n : ℕ, q ^ ((k + 1) * n) *
          ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖ := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [hn]
  calc ‖q‖ ^ ((k + 1) * (3 * k + 4) / 2) *
        ‖∑' n : ℕ, q ^ ((k + 1) * n) *
          ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖
      ≤ ‖q‖ ^ k * ‖∑' n : ℕ, q ^ ((k + 1) * n) *
          ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖ :=
        mul_le_mul_of_nonneg_right hpe (norm_nonneg _)
    _ ≤ ‖q‖ ^ k * (Real.exp (‖q‖ / (1 - ‖q‖)) * (1 - ‖q‖)⁻¹) :=
        mul_le_mul_of_nonneg_left hT (pow_nonneg hr0 k)

lemma penta_tail_tendsto (q : ℂ) (hq : ‖q‖ < 1) :
    Filter.Tendsto (fun k : ℕ => (-1 : ℂ) ^ (k + 1) * q ^ ((k + 1) * (3 * k + 4) / 2) *
      ∑' n : ℕ, q ^ ((k + 1) * n) *
        ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1)))
      Filter.atTop (nhds 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hg : Tendsto (fun k : ℕ => ‖q‖ ^ k *
      (Real.exp (‖q‖ / (1 - ‖q‖)) * (1 - ‖q‖)⁻¹)) atTop (nhds 0) := by
    have hpow : Tendsto (fun k : ℕ => ‖q‖ ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq
    simpa using hpow.mul_const (Real.exp (‖q‖ / (1 - ‖q‖)) * (1 - ‖q‖)⁻¹)
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => penta_tail_bound q hq k) hg

end Work.Haupt
