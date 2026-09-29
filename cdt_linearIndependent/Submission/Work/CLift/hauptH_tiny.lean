import Mathlib
import Submission.Work.CLift.bridge

namespace Work.CLift

open Submission.CDTPlan
open scoped BigOperators

/-!
# The tiny-norm estimate for the `Γ₀(2)` hauptmodul `h`

For `‖q‖ ≤ (3/4)·10⁻⁶` the hauptmodul `h(q) = -256 q ∏'ₙ (1+qⁿ⁺¹)²⁴` of
`Submission.CDTPlan` satisfies `‖h(q)‖ ≤ 2·10⁻⁴`.

The proof is elementary: each factor of the infinite product is bounded by
`‖1 + qⁿ⁺¹‖ ≤ 1 + ‖q‖ⁿ⁺¹ ≤ exp(‖q‖ⁿ⁺¹)`, and every finite partial product of
`∏ₙ ‖1+qⁿ⁺¹‖²⁴` is at most
`exp (24 · ∑ i ∈ s, ‖q‖^{i+1}) ≤ exp (24 ‖q‖/(1-‖q‖)) ≤ exp (1/26) ≤ 26/25`,
using `1/(1-r) = ∑ rⁿ` and `exp x ≤ 1/(1-x)`.
-/

/-- `exp x ≤ 1/(1-x)` for `x < 1` (from `1 - x ≤ exp(-x)`). -/
lemma exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have h2 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 : (1 - x) * Real.exp x ≤ 1 := by
    calc (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg x)
      _ = 1 := h2
  rw [le_div_iff₀ (by linarith)]
  nlinarith [h3]

/-- Every finite partial product of `∏'ₙ ‖1+qⁿ⁺¹‖²⁴` is bounded by `26/25`,
hence so is the infinite product (which is `≤ 26/25` even when it is not
multipliable). -/
lemma tprod_norm_pow_le (q : ℂ) (hq : ‖q‖ ≤ 3 / 4 * 10 ^ (-6 : ℤ)) :
    ∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24 ≤ 26 / 25 := by
  set r := ‖q‖ with hr
  have hr1e6 : r ≤ 1 / 1000000 := by
    have hle : (3 / 4 : ℝ) * 10 ^ (-6 : ℤ) ≤ 1 / 1000000 := by norm_num
    rw [hr]; linarith
  have hr0 : 0 ≤ r := by rw [hr]; exact norm_nonneg q
  have hr1000 : r ≤ 1 / 1000 := by linarith
  have hr1 : r < 1 := by linarith
  have hsum : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have hgeo : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
    exact (summable_nat_add_iff 1).2 hgeo
  have htsum : ∑' n : ℕ, r ^ (n + 1) = r / (1 - r) := by
    have hgeo : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
    have hfun : (fun n : ℕ => r ^ (n + 1)) = fun n : ℕ => r * r ^ n := by
      ext n
      rw [pow_succ']
    rw [hfun, tsum_mul_left, hgeo]
    rw [div_eq_mul_inv]
  have hkey : 24 * (r / (1 - r)) ≤ 1 / 26 := by
    have h1 : r / (1 - r) ≤ 2 * r := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hr0, hr1000]
    nlinarith [hr1e6, h1]
  have hexp : Real.exp (24 * (r / (1 - r))) ≤ 26 / 25 := by
    have hylt : 24 * (r / (1 - r)) < 1 := by linarith
    have h1 : (1 : ℝ) / (1 - 24 * (r / (1 - r))) ≤ 26 / 25 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 25)]
      linarith
    linarith [exp_le_inv_one_sub hylt]
  refine tprod_le_of_prod_le' (by norm_num : (1 : ℝ) ≤ 26 / 25) (fun s => ?_)
  calc ∏ i ∈ s, ‖1 + q ^ (i + 1)‖ ^ 24
      = (∏ i ∈ s, ‖1 + q ^ (i + 1)‖) ^ 24 := by rw [Finset.prod_pow]
    _ ≤ (∏ i ∈ s, (1 + r ^ (i + 1))) ^ 24 := by
        refine pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => norm_nonneg _) ?_ 24
        refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
        have h := norm_add_le (1 : ℂ) (q ^ (i + 1))
        rw [norm_one, norm_pow, ← hr] at h
        simpa using h
    _ ≤ (Real.exp (∑ i ∈ s, r ^ (i + 1))) ^ 24 := by
        refine pow_le_pow_left₀ (Finset.prod_nonneg fun i _ =>
          add_nonneg zero_le_one (pow_nonneg hr0 _)) ?_ 24
        exact Real.prod_one_add_le_exp_sum s (fun i => pow_nonneg hr0 _)
    _ = Real.exp (24 * ∑ i ∈ s, r ^ (i + 1)) := by
        rw [← Real.exp_nat_mul, Nat.cast_ofNat]
    _ ≤ Real.exp (24 * (r / (1 - r))) := by
        refine Real.exp_le_exp.mpr ?_
        have h := Summable.sum_le_tsum s (f := fun n : ℕ => r ^ (n + 1))
          (fun i _ => pow_nonneg hr0 _) hsum
        rw [htsum] at h
        linarith
    _ ≤ 26 / 25 := hexp

theorem hauptH_tiny (q : ℂ) (hq : ‖q‖ ≤ 3 / 4 * 10 ^ (-6 : ℤ)) : ‖hauptH q‖ ≤ 2 * 10 ^ (-4 : ℤ) := by
  have hsumq : Summable (fun n : ℕ => q ^ (n + 1)) := by
    have h2 : ‖q‖ < 1 := by
      have hle : (3 / 4 : ℝ) * 10 ^ (-6 : ℤ) < 1 := by norm_num
      linarith
    have hgeo : Summable (fun n : ℕ => q ^ n) := summable_geometric_iff_norm_lt_one.mpr h2
    exact (summable_nat_add_iff 1).2 hgeo
  have hg : Multipliable (fun n : ℕ => 1 + q ^ (n + 1)) :=
    Complex.multipliable_one_add_of_summable hsumq
  have hg24 : Multipliable (fun n : ℕ => (1 + q ^ (n + 1)) ^ 24) := hg.pow 24
  have hnorm : ‖∏' n : ℕ, (1 + q ^ (n + 1)) ^ 24‖ = ∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24 := by
    rw [hg24.norm_tprod]
    exact tprod_congr (fun n => by rw [norm_pow])
  have hH : ‖hauptH q‖ = 256 * ‖q‖ * ∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24 := by
    rw [Submission.CDTPlan.hauptH, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, hnorm]
  have hP := tprod_norm_pow_le q hq
  have h256 : (0:ℝ) ≤ 256 := by norm_num
  calc ‖hauptH q‖ = 256 * ‖q‖ * ∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24 := hH
    _ ≤ 256 * (3 / 4 * 10 ^ (-6 : ℤ)) * (26 / 25) := by
        have h1 : 256 * ‖q‖ ≤ 256 * (3 / 4 * 10 ^ (-6 : ℤ)) :=
          mul_le_mul_of_nonneg_left hq h256
        exact (mul_le_mul_of_nonneg_left hP (by positivity)).trans
          (mul_le_mul_of_nonneg_right h1 (by norm_num))
    _ ≤ 2 * 10 ^ (-4 : ℤ) := by norm_num

end Work.CLift
