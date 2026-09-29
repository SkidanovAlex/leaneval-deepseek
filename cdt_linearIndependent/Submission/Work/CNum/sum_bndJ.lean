import Mathlib
import Submission.Work.CNum.Jfun_defs
import Submission.Commons.Analysis.InfiniteSum.nat_sq_geom_hasSum
import Submission.Commons.Analysis.InfiniteSum.nat_mul_geom_hasSum

/-!
# `Work.CNum.sum_bndJ`: summability of `bndJ` and the numerical bound `6500`

`bndJ m` (see `Work.CNum.Jfun_defs`) is the dominating sequence for the second derivative
of the `Jfun` series:

`bndJ m = 24 * ( m(m-1) r^{m-2} u²/(1-rᵐ) + m r^{m-1} u/(1-rᵐ) + m² r^{2m-2} u²/(1-rᵐ)² )`

with `r = rJ = 79/100` and `u = uJ = 115/143`.

We prove `Σ_{m≥1} bndJ m ≤ 6500`.  The true value is `≈ 6010.92`, so the bound is generous
but not trivial: the naive estimate `1/(1-rᵐ) ≤ 1/(1-r)` overshoots by a factor `≈ 5`.
Instead we

* evaluate the head `Σ_{m<25} bndJ m` exactly by rational arithmetic (`≤ 5735`), and
* bound the tail, using `1/(1-r^{n+25}) ≤ 1/(1-r^{25})`, by the closed-form geometric sums
  `Σ n²rⁿ`, `Σ n rⁿ`, `Σ (r²)ⁿ` (`≤ 278`).
-/

namespace Work.CNum

open scoped BigOperators

/-! ## 1. The constants -/

private lemma rJ_pos : 0 < rJ := by norm_num [rJ]
private lemma rJ_lt_one : rJ < 1 := by norm_num [rJ]
private lemma rJ_nonneg : 0 ≤ rJ := le_of_lt rJ_pos
private lemma uJ_pos : 0 < uJ := by norm_num [uJ]

private lemma norm_rJ_lt_one : ‖rJ‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos rJ_pos]; exact rJ_lt_one

private lemma norm_rJ_sq_lt_one : ‖rJ ^ 2‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg rJ_nonneg 2)]
  norm_num [rJ]

private lemma rJ_pow_lt_one {m : ℕ} (hm : 1 ≤ m) : rJ ^ m < 1 :=
  pow_lt_one₀ rJ_nonneg rJ_lt_one (by omega)

private lemma bndJ_zero : bndJ 0 = 0 := by simp [bndJ]

/-! ## 2. The tail majorant at `m = 25`

For `n : ℕ` we bound `bndJ (n+25)` by replacing `1 - r^{n+25}` by `dJ = 1 - r^{25}` and the
exponents `r^{n+23}`, `r^{n+24}`, `r^{2n+48}` by `r²³ rⁿ`, `r²⁴ rⁿ`, `r⁴⁸ (r²)ⁿ`. -/

private noncomputable def dJ : ℝ := 1 - rJ ^ 25

private lemma dJ_pos : 0 < dJ := by
  have := rJ_pow_lt_one (m := 25) (by norm_num)
  simp only [dJ]; linarith

private noncomputable def a1 (n : ℕ) : ℝ :=
  ((n + 25 : ℕ) : ℝ) * (((n + 25 : ℕ) : ℝ) - 1) * rJ ^ n

private noncomputable def a2 (n : ℕ) : ℝ := ((n + 25 : ℕ) : ℝ) * rJ ^ n

private noncomputable def a3 (n : ℕ) : ℝ := ((n + 25 : ℕ) : ℝ) ^ 2 * (rJ ^ 2) ^ n

private noncomputable def C1 : ℝ := rJ ^ 23 * uJ ^ 2 / dJ

private noncomputable def C2 : ℝ := rJ ^ 24 * uJ / dJ

private noncomputable def C3 : ℝ := rJ ^ 48 * uJ ^ 2 / dJ ^ 2

private noncomputable def major (n : ℕ) : ℝ := 24 * (C1 * a1 n + C2 * a2 n + C3 * a3 n)

/-! ### 2.1 Closed forms for the three geometric sums -/

private noncomputable def v1 : ℝ :=
  rJ * (1 + rJ) / (1 - rJ) ^ 3 + (49 * (rJ / (1 - rJ) ^ 2) + 600 * (1 - rJ)⁻¹)

private noncomputable def v2 : ℝ := rJ / (1 - rJ) ^ 2 + 25 * (1 - rJ)⁻¹

private noncomputable def v3 : ℝ :=
  rJ ^ 2 * (1 + rJ ^ 2) / (1 - rJ ^ 2) ^ 3 +
    (50 * (rJ ^ 2 / (1 - rJ ^ 2) ^ 2) + 625 * (1 - rJ ^ 2)⁻¹)

private lemma a1_hasSum : HasSum a1 v1 := by
  have h1 : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * rJ ^ n) (rJ * (1 + rJ) / (1 - rJ) ^ 3) :=
    Commons.Analysis.InfiniteSum.nat_sq_geom_hasSum norm_rJ_lt_one
  have h2 : HasSum (fun n : ℕ => (n : ℝ) * rJ ^ n) (rJ / (1 - rJ) ^ 2) :=
    Commons.Analysis.InfiniteSum.nat_mul_geom_hasSum norm_rJ_lt_one
  have h0 : HasSum (fun n : ℕ => rJ ^ n) ((1 - rJ)⁻¹) :=
    hasSum_geometric_of_norm_lt_one norm_rJ_lt_one
  have hc : HasSum
      (fun n : ℕ => (n : ℝ) ^ 2 * rJ ^ n + (49 * ((n : ℝ) * rJ ^ n) + 600 * rJ ^ n))
      (rJ * (1 + rJ) / (1 - rJ) ^ 3 + (49 * (rJ / (1 - rJ) ^ 2) + 600 * (1 - rJ)⁻¹)) :=
    h1.add ((h2.mul_left 49).add (h0.mul_left 600))
  rw [v1]
  refine hc.congr_fun (fun n => ?_)
  simp only [a1]
  push_cast
  ring

private lemma a2_hasSum : HasSum a2 v2 := by
  have h2 : HasSum (fun n : ℕ => (n : ℝ) * rJ ^ n) (rJ / (1 - rJ) ^ 2) :=
    Commons.Analysis.InfiniteSum.nat_mul_geom_hasSum norm_rJ_lt_one
  have h0 : HasSum (fun n : ℕ => rJ ^ n) ((1 - rJ)⁻¹) :=
    hasSum_geometric_of_norm_lt_one norm_rJ_lt_one
  have hc : HasSum (fun n : ℕ => (n : ℝ) * rJ ^ n + 25 * rJ ^ n)
      (rJ / (1 - rJ) ^ 2 + 25 * (1 - rJ)⁻¹) :=
    h2.add (h0.mul_left 25)
  rw [v2]
  refine hc.congr_fun (fun n => ?_)
  simp only [a2]
  push_cast
  ring

private lemma a3_hasSum : HasSum a3 v3 := by
  have h1 : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (rJ ^ 2) ^ n)
      (rJ ^ 2 * (1 + rJ ^ 2) / (1 - rJ ^ 2) ^ 3) :=
    Commons.Analysis.InfiniteSum.nat_sq_geom_hasSum norm_rJ_sq_lt_one
  have h2 : HasSum (fun n : ℕ => (n : ℝ) * (rJ ^ 2) ^ n) (rJ ^ 2 / (1 - rJ ^ 2) ^ 2) :=
    Commons.Analysis.InfiniteSum.nat_mul_geom_hasSum norm_rJ_sq_lt_one
  have h0 : HasSum (fun n : ℕ => (rJ ^ 2) ^ n) ((1 - rJ ^ 2)⁻¹) :=
    hasSum_geometric_of_norm_lt_one norm_rJ_sq_lt_one
  have hc : HasSum
      (fun n : ℕ => (n : ℝ) ^ 2 * (rJ ^ 2) ^ n +
        (50 * ((n : ℝ) * (rJ ^ 2) ^ n) + 625 * (rJ ^ 2) ^ n))
      (rJ ^ 2 * (1 + rJ ^ 2) / (1 - rJ ^ 2) ^ 3 +
        (50 * (rJ ^ 2 / (1 - rJ ^ 2) ^ 2) + 625 * (1 - rJ ^ 2)⁻¹)) :=
    h1.add ((h2.mul_left 50).add (h0.mul_left 625))
  rw [v3]
  refine hc.congr_fun (fun n => ?_)
  simp only [a3]
  push_cast
  ring

private lemma major_hasSum : HasSum major (24 * (C1 * v1 + (C2 * v2 + C3 * v3))) := by
  have hc : HasSum (fun n : ℕ => 24 * (C1 * a1 n + (C2 * a2 n + C3 * a3 n)))
      (24 * (C1 * v1 + (C2 * v2 + C3 * v3))) :=
    ((a1_hasSum.mul_left C1).add
      ((a2_hasSum.mul_left C2).add (a3_hasSum.mul_left C3))).mul_left 24
  refine hc.congr_fun (fun n => ?_)
  unfold major
  ring

private lemma major_summable : Summable major := major_hasSum.summable

/-! ### 2.2 The pointwise bound `bndJ (n+25) ≤ major n` -/

private lemma pow_shift_two (n : ℕ) : rJ ^ (n + 25 - 2) = rJ ^ 23 * rJ ^ n := by
  rw [show n + 25 - 2 = 23 + n by omega, pow_add]

private lemma pow_shift_one (n : ℕ) : rJ ^ (n + 25 - 1) = rJ ^ 24 * rJ ^ n := by
  rw [show n + 25 - 1 = 24 + n by omega, pow_add]

private lemma pow_shift_double (n : ℕ) :
    rJ ^ (2 * (n + 25) - 2) = rJ ^ 48 * (rJ ^ 2) ^ n := by
  rw [show 2 * (n + 25) - 2 = 2 * n + 48 by omega, pow_add, ← pow_mul]
  ring

private lemma one_sub_pow_ge (n : ℕ) : dJ ≤ 1 - rJ ^ (n + 25) := by
  simp only [dJ]
  have h := pow_le_pow_of_le_one rJ_nonneg (le_of_lt rJ_lt_one) (show 25 ≤ n + 25 by omega)
  linarith

private lemma one_sub_pow_pos (n : ℕ) : 0 < 1 - rJ ^ (n + 25) := by
  have := rJ_pow_lt_one (m := n + 25) (by omega)
  linarith

private lemma shift_cast_one (n : ℕ) : (1 : ℝ) ≤ ((n + 25 : ℕ) : ℝ) := by
  exact_mod_cast (show 1 ≤ n + 25 by omega)

private lemma term1_le (n : ℕ) :
    ((n + 25 : ℕ) : ℝ) * (((n + 25 : ℕ) : ℝ) - 1) * rJ ^ (n + 25 - 2) * uJ ^ 2 /
        (1 - rJ ^ (n + 25)) ≤ C1 * a1 n := by
  have hc1 := shift_cast_one n
  have h0 : (0 : ℝ) ≤ ((n + 25 : ℕ) : ℝ) := by linarith
  have h1 : (0 : ℝ) ≤ ((n + 25 : ℕ) : ℝ) - 1 := by linarith
  rw [pow_shift_two n]
  have hnum : 0 ≤ ((n + 25 : ℕ) : ℝ) * (((n + 25 : ℕ) : ℝ) - 1) * (rJ ^ 23 * rJ ^ n) * uJ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg h0 h1)
      (mul_nonneg (pow_nonneg rJ_nonneg 23) (pow_nonneg rJ_nonneg n))) (sq_nonneg uJ)
  have hmain : ((n + 25 : ℕ) : ℝ) * (((n + 25 : ℕ) : ℝ) - 1) * (rJ ^ 23 * rJ ^ n) * uJ ^ 2 /
        (1 - rJ ^ (n + 25)) ≤
      ((n + 25 : ℕ) : ℝ) * (((n + 25 : ℕ) : ℝ) - 1) * (rJ ^ 23 * rJ ^ n) * uJ ^ 2 / dJ :=
    div_le_div_of_nonneg_left hnum dJ_pos (one_sub_pow_ge n)
  have heq : C1 * a1 n =
      ((n + 25 : ℕ) : ℝ) * (((n + 25 : ℕ) : ℝ) - 1) * (rJ ^ 23 * rJ ^ n) * uJ ^ 2 / dJ := by
    unfold C1 a1; ring
  rw [heq]; exact hmain

private lemma term2_le (n : ℕ) :
    ((n + 25 : ℕ) : ℝ) * rJ ^ (n + 25 - 1) * uJ / (1 - rJ ^ (n + 25)) ≤ C2 * a2 n := by
  have h0 : (0 : ℝ) ≤ ((n + 25 : ℕ) : ℝ) := by linarith [shift_cast_one n]
  rw [pow_shift_one n]
  have hnum : 0 ≤ ((n + 25 : ℕ) : ℝ) * (rJ ^ 24 * rJ ^ n) * uJ :=
    mul_nonneg (mul_nonneg h0 (mul_nonneg (pow_nonneg rJ_nonneg 24) (pow_nonneg rJ_nonneg n)))
      (le_of_lt uJ_pos)
  have hmain : ((n + 25 : ℕ) : ℝ) * (rJ ^ 24 * rJ ^ n) * uJ / (1 - rJ ^ (n + 25)) ≤
      ((n + 25 : ℕ) : ℝ) * (rJ ^ 24 * rJ ^ n) * uJ / dJ :=
    div_le_div_of_nonneg_left hnum dJ_pos (one_sub_pow_ge n)
  have heq : C2 * a2 n = ((n + 25 : ℕ) : ℝ) * (rJ ^ 24 * rJ ^ n) * uJ / dJ := by
    unfold C2 a2; ring
  rw [heq]; exact hmain

private lemma term3_le (n : ℕ) :
    ((n + 25 : ℕ) : ℝ) ^ 2 * rJ ^ (2 * (n + 25) - 2) * uJ ^ 2 /
        (1 - rJ ^ (n + 25)) ^ 2 ≤ C3 * a3 n := by
  rw [pow_shift_double n]
  have hnum : 0 ≤ ((n + 25 : ℕ) : ℝ) ^ 2 * (rJ ^ 48 * (rJ ^ 2) ^ n) * uJ ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _)
      (mul_nonneg (pow_nonneg rJ_nonneg 48) (pow_nonneg (sq_nonneg rJ) n))) (sq_nonneg uJ)
  have hge2 : dJ ^ 2 ≤ (1 - rJ ^ (n + 25)) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt dJ_pos) (one_sub_pow_ge n) 2
  have hmain : ((n + 25 : ℕ) : ℝ) ^ 2 * (rJ ^ 48 * (rJ ^ 2) ^ n) * uJ ^ 2 /
        (1 - rJ ^ (n + 25)) ^ 2 ≤
      ((n + 25 : ℕ) : ℝ) ^ 2 * (rJ ^ 48 * (rJ ^ 2) ^ n) * uJ ^ 2 / dJ ^ 2 :=
    div_le_div_of_nonneg_left hnum (pow_pos dJ_pos 2) hge2
  have heq : C3 * a3 n = ((n + 25 : ℕ) : ℝ) ^ 2 * (rJ ^ 48 * (rJ ^ 2) ^ n) * uJ ^ 2 / dJ ^ 2 := by
    unfold C3 a3; ring
  rw [heq]; exact hmain

private lemma bndJ_le_major (n : ℕ) : bndJ (n + 25) ≤ major n := by
  have h1 := term1_le n
  have h2 := term2_le n
  have h3 := term3_le n
  unfold bndJ major
  linarith [h1, h2, h3]

private lemma bndJ_shift_nonneg (n : ℕ) : 0 ≤ bndJ (n + 25) := by
  have h0 : (0 : ℝ) ≤ ((n + 25 : ℕ) : ℝ) := by linarith [shift_cast_one n]
  have h1 : (0 : ℝ) ≤ ((n + 25 : ℕ) : ℝ) - 1 := by linarith [shift_cast_one n]
  have hden : (0 : ℝ) ≤ 1 - rJ ^ (n + 25) := le_of_lt (one_sub_pow_pos n)
  unfold bndJ
  refine mul_nonneg (by norm_num) (add_nonneg (add_nonneg ?_ ?_) ?_)
  · exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h0 h1) (pow_nonneg rJ_nonneg _))
      (sq_nonneg uJ)) hden
  · exact div_nonneg (mul_nonneg (mul_nonneg h0 (pow_nonneg rJ_nonneg _)) (le_of_lt uJ_pos)) hden
  · exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg rJ_nonneg _))
      (sq_nonneg uJ)) (sq_nonneg _)

/-! ### 2.3 Numerics -/

private lemma v1_le : v1 ≤ 3888 := by simp only [v1, rJ]; norm_num

private lemma v2_le : v2 ≤ 137 := by simp only [v2, rJ]; norm_num

private lemma v3_le : v3 ≤ 1903 := by simp only [v3, rJ]; norm_num

private lemma C1_nonneg : 0 ≤ C1 := by
  unfold C1
  exact div_nonneg (mul_nonneg (pow_nonneg rJ_nonneg 23) (sq_nonneg uJ)) (le_of_lt dJ_pos)

private lemma C2_nonneg : 0 ≤ C2 := by
  unfold C2
  exact div_nonneg (mul_nonneg (pow_nonneg rJ_nonneg 24) (le_of_lt uJ_pos)) (le_of_lt dJ_pos)

private lemma C3_nonneg : 0 ≤ C3 := by
  unfold C3
  exact div_nonneg (mul_nonneg (pow_nonneg rJ_nonneg 48) (sq_nonneg uJ)) (sq_nonneg _)

private lemma major_tsum_le : (∑' n : ℕ, major n) ≤ 278 := by
  rw [major_hasSum.tsum_eq]
  have h1 : C1 * v1 ≤ C1 * 3888 := mul_le_mul_of_nonneg_left v1_le C1_nonneg
  have h2 : C2 * v2 ≤ C2 * 137 := mul_le_mul_of_nonneg_left v2_le C2_nonneg
  have h3 : C3 * v3 ≤ C3 * 1903 := mul_le_mul_of_nonneg_left v3_le C3_nonneg
  have hnum : 24 * (C1 * 3888 + (C2 * 137 + C3 * 1903)) ≤ 278 := by
    simp only [C1, C2, C3, dJ, rJ, uJ]
    norm_num
  linarith [h1, h2, h3, hnum]

private lemma tail_bound : (∑' n : ℕ, bndJ (n + 25)) ≤ 278 := by
  have hs : Summable (fun n : ℕ => bndJ (n + 25)) :=
    Summable.of_nonneg_of_le bndJ_shift_nonneg bndJ_le_major major_summable
  calc (∑' n : ℕ, bndJ (n + 25)) ≤ (∑' n : ℕ, major n) :=
        hs.tsum_le_tsum (fun n => bndJ_le_major n) major_summable
    _ ≤ 278 := major_tsum_le

private lemma head_bound : (∑ i ∈ Finset.range 25, bndJ i) ≤ 5735 := by
  simp only [bndJ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, rJ, uJ]
  norm_num

/-! ## 3. The theorem -/

theorem sum_bndJ : Summable (fun m : ℕ => bndJ (m + 1)) ∧ (∑' m : ℕ, bndJ (m + 1)) ≤ 6500 := by
  have htail_summ : Summable (fun n : ℕ => bndJ (n + 25)) :=
    Summable.of_nonneg_of_le bndJ_shift_nonneg bndJ_le_major major_summable
  have hb : Summable (fun m : ℕ => bndJ m) := (summable_nat_add_iff 25).mp htail_summ
  have hsumm : Summable (fun m : ℕ => bndJ (m + 1)) := (summable_nat_add_iff 1).mpr hb
  refine ⟨hsumm, ?_⟩
  have hshift : (∑' m : ℕ, bndJ (m + 1)) = ∑' m : ℕ, bndJ m := by
    have h := hb.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at h
    rw [bndJ_zero, zero_add] at h
    exact h
  rw [hshift]
  have hsplit := hb.sum_add_tsum_nat_add 25
  have hhead : (∑ i ∈ Finset.range 25, bndJ i) ≤ 5735 := head_bound
  have htail : (∑' n : ℕ, bndJ (n + 25)) ≤ 278 := tail_bound
  linarith

end Work.CNum
