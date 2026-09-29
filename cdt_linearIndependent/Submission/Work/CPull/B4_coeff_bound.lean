import Mathlib
import Submission.Work.Pure.b4_eq_prod

/-!
# Coefficient bound for the pure function `B₄`

`Submission.CDTPlan.B4` is the pure function of Calegari--Dimitrov--Tang,

`B₄ = 4 Σ_{n≥0} y^{n+1}/16ⁿ Σ_k C(2k,k)·C(2n-2k,n-k)/((2k-1)(2n-2k+1)²)`

(paper eq. `(defB)`).  Writing `cₘ = [yᵐ]B₄` we prove the geometric coefficient bound

`|cₘ| ≤ 4·(m+1)·(1/4)ᵐ`,   hence   `‖cₙ‖ ≤ 16·(1/2)ⁿ` for all `n`.

The estimate is completely elementary.  For `m = n-1` and `j = n-1-k` the summand of
`c_{m+1}` is `C(2k,k)·C(2j,j) / ((2k-1)(2j+1)²)`; the absolute value of the denominator is
`≥ 1`, while `C(2r,r) ≤ 4ʳ` (`Nat.centralBinom_le_four_pow`).  Hence every one of the `m+1`
summands is bounded by `4ᵏ·4ʲ = 4ᵐ`, so `|c_{m+1}| ≤ 4·16^{-m}·(m+1)·4ᵐ = 4(m+1)4^{-m}`.
Finally `4(m+1)4^{-m} ≤ 8·2^{-m} = 16·2^{-(m+1)}` because `m+1 ≤ 2^{m+1}`.
-/

namespace Work.CPull

open PowerSeries
open scoped BigOperators

/-- Every summand of the defining double sum of `B₄` is bounded by `4ᵐ`:
the absolute value of the denominator is at least `1`, and each central binomial
coefficient `C(2r,r)` is at most `4ʳ`. -/
private lemma term_abs_le (m k : ℕ) (hk : k ≤ m) :
    |((Nat.centralBinom k : ℚ) * (Nat.centralBinom (m - k) : ℚ) /
      ((2 * (k : ℚ) - 1) * (2 * ((m - k : ℕ) : ℚ) + 1) ^ 2))| ≤ (4 : ℚ) ^ m := by
  have hnum_nonneg : (0:ℚ) ≤ (Nat.centralBinom k : ℚ) * (Nat.centralBinom (m-k) : ℚ) := by
    positivity
  have hden_ge_one : (1:ℚ) ≤ |(2 * (k:ℚ) - 1) * (2 * ((m-k:ℕ):ℚ) + 1)^2| := by
    rw [abs_mul]
    have h1 : (1:ℚ) ≤ |2 * (k:ℚ) - 1| := by
      match k with
      | 0 => norm_num
      | (j+1) =>
        have hk1 : (2 * ((j+1 : ℕ) : ℚ) - 1) = 2*(j:ℚ) + 1 := by push_cast; ring
        rw [hk1, abs_of_nonneg (by positivity)]
        have : (0:ℚ) ≤ (j:ℚ) := Nat.cast_nonneg j
        linarith
    have h2 : (1:ℚ) ≤ |(2 * ((m-k:ℕ):ℚ) + 1)^2| := by
      rw [abs_of_nonneg (by positivity)]
      have h3 : (1:ℚ) ≤ 2 * ((m-k:ℕ):ℚ) + 1 := by
        have : (0:ℚ) ≤ ((m-k:ℕ):ℚ) := Nat.cast_nonneg _
        linarith
      nlinarith [h3]
    calc (1:ℚ) = 1 * 1 := by ring
      _ ≤ |2 * (k:ℚ) - 1| * |(2 * ((m-k:ℕ):ℚ)+1)^2| :=
            mul_le_mul h1 h2 (by norm_num) (abs_nonneg _)
  calc |(Nat.centralBinom k : ℚ) * (Nat.centralBinom (m-k) : ℚ) /
          ((2 * (k:ℚ)-1) * (2*((m-k:ℕ):ℚ)+1)^2)|
      = |(Nat.centralBinom k : ℚ) * (Nat.centralBinom (m-k) : ℚ)| /
          |((2 * (k:ℚ)-1) * (2*((m-k:ℕ):ℚ)+1)^2)| := abs_div _ _
    _ ≤ |(Nat.centralBinom k : ℚ) * (Nat.centralBinom (m-k) : ℚ)| / 1 :=
          div_le_div_of_nonneg_left (abs_nonneg _) one_pos hden_ge_one
    _ = (Nat.centralBinom k : ℚ) * (Nat.centralBinom (m-k) : ℚ) := by
          rw [div_one, abs_of_nonneg hnum_nonneg]
    _ ≤ (4:ℚ)^k * (4:ℚ)^(m-k) := by
          apply mul_le_mul
          · have h := Nat.centralBinom_le_four_pow k
            have : ((Nat.centralBinom k : ℕ) : ℚ) ≤ ((4^k : ℕ) : ℚ) := by exact_mod_cast h
            simpa using this
          · have h := Nat.centralBinom_le_four_pow (m-k)
            have : ((Nat.centralBinom (m-k) : ℕ) : ℚ) ≤ ((4^(m-k) : ℕ) : ℚ) := by exact_mod_cast h
            simpa using this
          · positivity
          · positivity
    _ = (4:ℚ)^m := by rw [← pow_add, Nat.add_sub_cancel' hk]

/-- The coefficients of `B₄` decay at least like `4(m+1)·4^{-m}`. -/
private lemma coeff_abs_le (m : ℕ) :
    |PowerSeries.coeff (m+1) Submission.CDTPlan.B4| ≤ 4 * ((m+1 : ℕ) : ℚ) * (1/4)^m := by
  rw [Work.Pure.coeff_succ_B4 m]
  have hterm : ∀ k ∈ Finset.range (m+1),
      |(↑k.centralBinom * ↑(m - k).centralBinom /
        ((2 * ↑k - 1) * (2 * ↑(m - k) + 1) ^ 2) : ℚ)| ≤ (4:ℚ)^m := by
    intro k hk
    exact term_abs_le m k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hsum : |∑ k ∈ Finset.range (m+1),
      (↑k.centralBinom * ↑(m - k).centralBinom /
        ((2 * ↑k - 1) * (2 * ↑(m - k) + 1) ^ 2) : ℚ)| ≤ ((m+1 : ℕ) : ℚ) * 4^m := by
    calc |∑ k ∈ Finset.range (m+1), (↑k.centralBinom * ↑(m - k).centralBinom /
            ((2 * ↑k - 1) * (2 * ↑(m - k) + 1) ^ 2) : ℚ)|
        ≤ ∑ k ∈ Finset.range (m+1), |(↑k.centralBinom * ↑(m - k).centralBinom /
            ((2 * ↑k - 1) * (2 * ↑(m - k) + 1) ^ 2) : ℚ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (m+1), (4:ℚ)^m := Finset.sum_le_sum hterm
      _ = ((m+1 : ℕ) : ℚ) * 4^m := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h4pos : (0:ℚ) ≤ 4/16^m := by positivity
  calc |4 / 16 ^ m * ∑ k ∈ Finset.range (m + 1), (↑k.centralBinom * ↑(m - k).centralBinom /
          ((2 * ↑k - 1) * (2 * ↑(m - k) + 1) ^ 2) : ℚ)|
      = |4 / 16 ^ m| * |∑ k ∈ Finset.range (m + 1), (↑k.centralBinom * ↑(m - k).centralBinom /
          ((2 * ↑k - 1) * (2 * ↑(m - k) + 1) ^ 2) : ℚ)| := abs_mul _ _
    _ = 4 / 16 ^ m * |∑ k ∈ Finset.range (m + 1), (↑k.centralBinom * ↑(m - k).centralBinom /
          ((2 * ↑k - 1) * (2 * ↑(m - k) + 1) ^ 2) : ℚ)| := by
          rw [abs_of_nonneg h4pos]
    _ ≤ 4 / 16 ^ m * (((m+1 : ℕ) : ℚ) * 4^m) := mul_le_mul_of_nonneg_left hsum h4pos
    _ = 4 * ((m+1 : ℕ) : ℚ) * (1/4)^m := by
          have h16 : (16:ℚ)^m = 4^m * 4^m := by rw [← mul_pow]; norm_num
          rw [h16, div_eq_mul_inv, div_pow, one_pow, one_div]
          field_simp

/-- The numerical inequality `4(m+1)4^{-m} ≤ 8·2^{-m}`, an immediate consequence of
`m + 1 ≤ 2^{m+1}`. -/
private lemma four_pow_bound (m : ℕ) :
    (4:ℝ) * ((m:ℝ)+1) * (1/4)^m ≤ 8 * (1/2)^m := by
  have hb : ((m:ℝ)+1) * (1/2:ℝ)^(m+1) ≤ 1 := by
    have h : (m + 1 : ℕ) ≤ 2 ^ (m + 1) := by
      have h := Nat.choose_le_two_pow (m+1) 1
      rwa [Nat.choose_one_right] at h
    have hR : ((m:ℝ)+1) ≤ 2 ^ (m+1) := by
      have : ((m + 1 : ℕ) : ℝ) ≤ ((2 ^ (m+1) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this ⊢
      linarith
    have hpos : (0:ℝ) < 2^(m+1) := by positivity
    calc ((m:ℝ)+1) * (1/2:ℝ)^(m+1) = ((m:ℝ)+1) / 2^(m+1) := by
          rw [div_pow, one_pow]; ring
      _ ≤ 1 := by rw [div_le_one hpos]; exact hR
  have hp_pos : (0:ℝ) < (1/2:ℝ)^(m+1) := by positivity
  have hstep : ((m:ℝ)+1) * ((1/2:ℝ)^(m+1))^2 ≤ (1/2:ℝ)^(m+1) := by
    calc ((m:ℝ)+1) * ((1/2:ℝ)^(m+1))^2
        = (((m:ℝ)+1) * (1/2:ℝ)^(m+1)) * (1/2:ℝ)^(m+1) := by ring
      _ ≤ 1 * (1/2:ℝ)^(m+1) := mul_le_mul hb le_rfl hp_pos.le (by norm_num)
      _ = (1/2:ℝ)^(m+1) := one_mul _
  have h4 : (1/4:ℝ)^m = 4 * ((1/2:ℝ)^(m+1))^2 := by
    have e1 : (1/4:ℝ)^m = (1/2:ℝ)^(2*m) := by
      rw [show (1/4:ℝ) = (1/2)^2 by norm_num, ← pow_mul]
    have e2 : 4 * ((1/2:ℝ)^(m+1))^2 = (1/2:ℝ)^(2*m) := by
      rw [← pow_mul, show (m+1)*2 = 2*m + 2 by omega, pow_add]
      norm_num
      ring
    rw [e1, e2]
  have h2 : (1/2:ℝ)^m = 2 * (1/2:ℝ)^(m+1) := by
    rw [pow_succ]; ring
  rw [h4, h2]
  linarith [hstep]

theorem B4_coeff_bound :
    ∀ n : ℕ, ‖((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ)‖ ≤ 16 * (1 / 2 : ℝ) ^ n := by
  intro n
  rcases n with _ | m
  · have hzero : ((PowerSeries.coeff 0 Submission.CDTPlan.B4 : ℚ) : ℂ) = 0 := by
      simp [Submission.CDTPlan.B4]
    rw [hzero, norm_zero]
    norm_num
  · have hnorm : ‖((PowerSeries.coeff (m+1) Submission.CDTPlan.B4 : ℚ) : ℂ)‖ =
        ((|PowerSeries.coeff (m+1) Submission.CDTPlan.B4| : ℚ) : ℝ) := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, Rat.cast_abs]
    rw [hnorm]
    calc ((|PowerSeries.coeff (m+1) Submission.CDTPlan.B4| : ℚ) : ℝ)
        ≤ ((4 * ((m+1 : ℕ) : ℚ) * (1/4:ℚ)^m : ℚ) : ℝ) := by exact_mod_cast coeff_abs_le m
      _ = 4 * ((m:ℝ)+1) * (1/4:ℝ)^m := by push_cast; ring
      _ ≤ 8 * (1/2:ℝ)^m := four_pow_bound m
      _ ≤ 16 * (1/2:ℝ)^(m+1) := by rw [pow_succ]; linarith

end Work.CPull
