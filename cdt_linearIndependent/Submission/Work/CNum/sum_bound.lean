import Mathlib
import Submission.Work.CNum.Hfun_defs
import Submission.Commons.Analysis.InfiniteSum.nat_sq_geom_hasSum

/-!
# Bound on `Σ' n, 24 (n+1)² r^(n+1) / (1 - r^(n+1))²` for `r = 3/4`

We split the sum at `k = 16`, evaluate the head by rational arithmetic, and bound the
tail by `(1 - r¹⁶)⁻² · Σ_{k≥16} 24 k² rᵏ`, using the closed form
`Σ_k k² rᵏ = r(1+r)/(1-r)³ = 84` for `r = 3/4`.
-/

namespace Work.CNum

open scoped BigOperators

/-- The geometric factor `24 k² rᵏ`. -/
private noncomputable def gterm (k : ℕ) : ℝ := 24 * (k : ℝ) ^ 2 * r34 ^ k

/-- The `k`-th summand `24 k² rᵏ / (1 - rᵏ)²`. -/
private noncomputable def hterm (k : ℕ) : ℝ := gterm k / (1 - r34 ^ k) ^ 2

private lemma norm_r34_lt_one : ‖r34‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos r34_pos]; exact r34_lt_one

private lemma gterm_nonneg (k : ℕ) : 0 ≤ gterm k := by
  unfold gterm
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (pow_nonneg r34_nonneg k)

private lemma gterm_summable : Summable gterm := by
  have h := (summable_pow_mul_geometric_of_norm_lt_one 2 (r := r34) norm_r34_lt_one).mul_left
    (24 : ℝ)
  refine h.congr (fun k => ?_)
  unfold gterm; ring

private lemma gterm_tsum : (∑' k : ℕ, gterm k) = 2016 := by
  have h := Commons.Analysis.InfiniteSum.nat_sq_geom_hasSum (X := r34) norm_r34_lt_one
  have hv : r34 * (1 + r34) / (1 - r34) ^ 3 = (84 : ℝ) := by norm_num [r34]
  rw [hv] at h
  have h2 := h.mul_left (24 : ℝ)
  have h3 : (24 : ℝ) * 84 = 2016 := by norm_num
  rw [h3] at h2
  have hfun : (fun k : ℕ => 24 * ((k : ℝ) ^ 2 * r34 ^ k)) = gterm := by
    funext k; unfold gterm; ring
  rw [hfun] at h2
  exact h2.tsum_eq

private lemma hterm_nonneg (k : ℕ) : 0 ≤ hterm k := by
  unfold hterm
  exact div_nonneg (gterm_nonneg k) (sq_nonneg _)

private lemma hterm_le_gterm (k : ℕ) : hterm k ≤ 16 * gterm k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [hterm, gterm]
  · have hle : r34 ^ k ≤ r34 := by
      simpa using (pow_le_pow_of_le_one r34_nonneg (le_of_lt r34_lt_one) hk)
    have hlt : (0 : ℝ) < 1 - r34 ^ k := by
      have := r34_pow_lt_one hk; linarith
    have hge : (1 / 4 : ℝ) ≤ 1 - r34 ^ k := by
      have h1 : (1 : ℝ) / 4 = 1 - r34 := by norm_num [r34]
      rw [h1]; linarith
    have h16 : 1 / (1 - r34 ^ k) ^ 2 ≤ 16 := by
      rw [div_le_iff₀ (pow_pos hlt 2)]
      have h2 : ((1 : ℝ) / 4) ^ 2 ≤ (1 - r34 ^ k) ^ 2 := pow_le_pow_left₀ (by norm_num) hge 2
      nlinarith [h2]
    have hX : 0 ≤ gterm k := gterm_nonneg k
    unfold hterm
    calc gterm k / (1 - r34 ^ k) ^ 2 = gterm k * (1 / (1 - r34 ^ k) ^ 2) := by ring
      _ ≤ gterm k * 16 := mul_le_mul_of_nonneg_left h16 hX
      _ = 16 * gterm k := by ring

private lemma hterm_summable : Summable hterm := by
  refine Summable.of_nonneg_of_le hterm_nonneg (fun k => hterm_le_gterm k) ?_
  exact gterm_summable.mul_left 16

private lemma hterm_zero : hterm 0 = 0 := by
  simp [hterm, gterm]

private lemma headA_bound : (∑ k ∈ Finset.range 16, hterm k) ≤ 2810 := by
  simp only [hterm, gterm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, r34]
  norm_num

private lemma headB_lower : (1657 : ℝ) ≤ ∑ k ∈ Finset.range 16, gterm k := by
  simp only [gterm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, r34]
  norm_num

private lemma headB_upper : (∑ k ∈ Finset.range 16, gterm k) ≤ 2016 := by
  simp only [gterm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, r34]
  norm_num

private lemma D_le : 1 / (1 - r34 ^ 16) ^ 2 ≤ (1.021 : ℝ) := by
  norm_num [r34]

/-- Bound on the `k ≥ 16` part of the sum. -/
private lemma tail_bound :
    (∑' i : ℕ, hterm (i + 16)) ≤
      (1 / (1 - r34 ^ 16) ^ 2) * (2016 - ∑ k ∈ Finset.range 16, gterm k) := by
  have htf : Summable (fun i : ℕ => hterm (i + 16)) := (summable_nat_add_iff 16).2 hterm_summable
  have htg : Summable (fun i : ℕ => (1 / (1 - r34 ^ 16) ^ 2) * gterm (i + 16)) :=
    ((summable_nat_add_iff 16).2 gterm_summable).mul_left _
  have hle : ∀ i : ℕ, hterm (i + 16) ≤ (1 / (1 - r34 ^ 16) ^ 2) * gterm (i + 16) := by
    intro i
    have hm : r34 ^ (i + 16) ≤ r34 ^ 16 :=
      pow_le_pow_of_le_one r34_nonneg (le_of_lt r34_lt_one) (by omega)
    have hpos : (0 : ℝ) < 1 - r34 ^ 16 := by
      have := r34_pow_lt_one (by norm_num : 1 ≤ 16); linarith
    have hge : 1 - r34 ^ 16 ≤ 1 - r34 ^ (i + 16) := by linarith
    have h2 : (1 - r34 ^ 16) ^ 2 ≤ (1 - r34 ^ (i + 16)) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hpos) hge 2
    have hrec : 1 / (1 - r34 ^ (i + 16)) ^ 2 ≤ 1 / (1 - r34 ^ 16) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) h2
    have hX : 0 ≤ gterm (i + 16) := gterm_nonneg _
    unfold hterm
    calc gterm (i + 16) / (1 - r34 ^ (i + 16)) ^ 2
        = gterm (i + 16) * (1 / (1 - r34 ^ (i + 16)) ^ 2) := by ring
      _ ≤ gterm (i + 16) * (1 / (1 - r34 ^ 16) ^ 2) := mul_le_mul_of_nonneg_left hrec hX
      _ = (1 / (1 - r34 ^ 16) ^ 2) * gterm (i + 16) := by ring
  have htg' : Summable (fun i : ℕ => gterm (i + 16)) := (summable_nat_add_iff 16).2 gterm_summable
  calc (∑' i : ℕ, hterm (i + 16))
      ≤ (∑' i : ℕ, (1 / (1 - r34 ^ 16) ^ 2) * gterm (i + 16)) := htf.tsum_le_tsum hle htg
    _ = (1 / (1 - r34 ^ 16) ^ 2) * (∑' i : ℕ, gterm (i + 16)) :=
          Summable.tsum_mul_left _ htg'
    _ = (1 / (1 - r34 ^ 16) ^ 2) * (2016 - ∑ k ∈ Finset.range 16, gterm k) := by
          congr 1
          have hsp := gterm_summable.sum_add_tsum_nat_add 16
          rw [gterm_tsum] at hsp
          linarith

theorem sum_bound :
    (∑' n : ℕ, 24 * ((n : ℝ) + 1) ^ 2 * r34 ^ (n + 1) / (1 - r34 ^ (n + 1)) ^ 2) ≤ 3200 := by
  have hsummand : ∀ n : ℕ,
      24 * ((n : ℝ) + 1) ^ 2 * r34 ^ (n + 1) / (1 - r34 ^ (n + 1)) ^ 2 = hterm (n + 1) := by
    intro n; unfold hterm gterm; push_cast; ring
  rw [tsum_congr hsummand]
  have hshift : (∑' n : ℕ, hterm (n + 1)) = ∑' k : ℕ, hterm k := by
    have h := hterm_summable.sum_add_tsum_nat_add 1
    simpa [Finset.sum_range_one, hterm_zero] using h
  rw [hshift, ← hterm_summable.sum_add_tsum_nat_add 16]
  have hhead : (∑ k ∈ Finset.range 16, hterm k) ≤ 2810 := headA_bound
  have htail : (∑' i : ℕ, hterm (i + 16)) ≤
      (1 / (1 - r34 ^ 16) ^ 2) * (2016 - ∑ k ∈ Finset.range 16, gterm k) := tail_bound
  have htail2 : (1 / (1 - r34 ^ 16) ^ 2) * (2016 - ∑ k ∈ Finset.range 16, gterm k)
      ≤ (1.021 : ℝ) * 359 := by
    have hc1 : (0 : ℝ) ≤ 2016 - ∑ k ∈ Finset.range 16, gterm k := by linarith [headB_upper]
    have hc2 : 2016 - ∑ k ∈ Finset.range 16, gterm k ≤ 359 := by linarith [headB_lower]
    calc (1 / (1 - r34 ^ 16) ^ 2) * (2016 - ∑ k ∈ Finset.range 16, gterm k)
        ≤ 1.021 * (2016 - ∑ k ∈ Finset.range 16, gterm k) := mul_le_mul_of_nonneg_right D_le hc1
      _ ≤ 1.021 * 359 := mul_le_mul_of_nonneg_left hc2 (by norm_num)
  linarith [hhead, htail, htail2]

end Work.CNum
