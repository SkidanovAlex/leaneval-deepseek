import Mathlib

namespace Work.LinnikAreas.DhExplicit

set_option maxHeartbeats 1600000

/-- `log(2 + a + 2^k) + 2 ≤ (k+2)·(log(2+a) + 2)` for `a ≥ 0`. -/
lemma log_two_add_pow_le (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    Real.log (2 + a + (2:ℝ)^k) + 2 ≤ ((k:ℝ) + 2) * (Real.log (2 + a) + 2) := by
  have hbase : (0:ℝ) < 2 + a := by linarith
  have hpow : (0:ℝ) < (2:ℝ)^k := by positivity
  have hle : 2 + a + (2:ℝ)^k ≤ (2 + a) * (2 * (2:ℝ)^k) := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simp; linarith
    · have h2k : (2:ℝ) ≤ (2:ℝ)^k := by
        calc (2:ℝ) = (2:ℝ)^1 := by ring
          _ ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hpos
      nlinarith [ha, h2k]
  have hlog := Real.log_le_log (by positivity) hle
  rw [Real.log_mul (ne_of_gt hbase) (by positivity : (2 * (2:ℝ)^k) ≠ 0),
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hpow), Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hka : 0 ≤ Real.log (2 + a) := Real.log_nonneg (by linarith)
  have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
  have h1 : Real.log (2 + a + (2:ℝ)^k) ≤ Real.log (2 + a) + (k:ℝ) + 1 := by
    nlinarith [hlog, hlog2, hk0]
  nlinarith [h1, hka, hk0]

/-- `log(x + 2^k + 2) + L + 2 ≤ (k+2)·(L + log(2+x) + 2)` for `x, L ≥ 0`. -/
lemma log_add_pow_add_le (x L : ℝ) (hx : 0 ≤ x) (hL : 0 ≤ L) (k : ℕ) :
    Real.log (x + (2:ℝ)^k + 2) + L + 2 ≤ ((k:ℝ) + 2) * (L + Real.log (2 + x) + 2) := by
  have h1 := log_two_add_pow_le x hx k
  have harg : x + (2:ℝ)^k + 2 = 2 + x + (2:ℝ)^k := by ring
  rw [harg]
  have hkL : (0:ℝ) ≤ (k:ℝ) * L := mul_nonneg (by positivity) hL
  nlinarith [h1, hkL]

/-- `∑_{k ≤ K} (k+2)·(1/2)^k ≤ 6`. -/
lemma sum_kp2_half_le (K : ℕ) :
    ∑ k ∈ Finset.range (K+1), ((k:ℝ) + 2) * ((1/2:ℝ)^k) ≤ 6 := by
  have hsumm1 : Summable (fun k : ℕ => ((k:ℝ) + 1) * ((1/2:ℝ)^k)) := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := (1/2:ℝ)) (by norm_num)
    simpa [Nat.choose_one_right, mul_comm] using h.summable
  have hval1 : (∑' k : ℕ, ((k:ℝ) + 1) * ((1/2:ℝ)^k)) = 4 := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := (1/2:ℝ)) (by norm_num)
    rw [show (1:ℝ)/(1-(1/2:ℝ))^(1+1) = 4 by norm_num] at h
    have h' := h.tsum_eq
    simpa [Nat.choose_one_right, mul_comm] using h'
  have hsumm2 : Summable (fun k : ℕ => ((1/2:ℝ)^k)) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hval2 : (∑' k : ℕ, ((1/2:ℝ)^k)) = 2 := tsum_geometric_two
  have hsumm : Summable (fun k : ℕ => ((k:ℝ) + 2) * ((1/2:ℝ)^k)) := by
    have h := hsumm1.add hsumm2
    refine h.congr ?_
    intro k; ring
  have hval : (∑' k : ℕ, ((k:ℝ) + 2) * ((1/2:ℝ)^k)) = 6 := by
    have hcongr : (∑' k : ℕ, ((k:ℝ) + 2) * ((1/2:ℝ)^k))
        = ∑' k : ℕ, (((k:ℝ)+1)*((1/2:ℝ)^k) + ((1/2:ℝ)^k)) := by
      apply tsum_congr; intro k; ring
    rw [hcongr, Summable.tsum_add hsumm1 hsumm2, hval1, hval2]
    norm_num
  exact le_trans (Summable.sum_le_tsum (Finset.range (K+1))
    (f := fun k : ℕ => ((k:ℝ) + 2) * ((1/2:ℝ)^k)) (fun i _ => by positivity) hsumm)
    (le_of_eq hval)

/-!
Elementary real-arithmetic estimate for the dyadic inverse-square decomposition of a zero sum.

For `x ≥ 0`, `L ≥ 0`, `A ≥ 0` and every `K : ℕ`,
`∑_{k ≤ K} (4/4^k) · A · (2^k + 1) · (log (x + 2^k + 2) + L + 2) ≤ C · A · (L + log (2+x) + 2)`
for an absolute constant `C > 0`.

Sketch: `4/4^k · (2^k+1) = 4/2^k + 4/4^k + 4·2^k/4^k`, and the series `∑ 4/2^k`, `∑ 4/4^k`,
`∑ 4(k+1)/2^k`, `∑ 4(k+1)/4^k` converge with small explicit sums; `log (x + 2^k + 2) ≤ log (2+x) + (k+1)·log 2`
because `x + 2^k + 2 ≤ (2+x)(2^k+1)`; and `L + log (2+x) + 2 ≥ 2 + log 2` absorbs the constant term.
(This mirrors `Work.LinnikAreas.FarRepel.dyadic_arith` in
`Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound`, which may be read but not imported.)
-/
theorem dyadicBallSumLe : ∃ C : ℝ, 0 < C ∧ ∀ (x L A : ℝ), 0 ≤ x → 0 ≤ L → 0 ≤ A → ∀ K : ℕ,
    (∑ k ∈ Finset.range (K + 1),
        (4 / (4 : ℝ) ^ k) * (A * ((2 : ℝ) ^ k + 1) * (Real.log (x + (2 : ℝ) ^ k + 2) + L + 2)))
      ≤ C * A * (L + Real.log (2 + x) + 2) := by
  refine ⟨50, by norm_num, ?_⟩
  intro x L A hx hL hA K
  set M : ℝ := L + Real.log (2 + x) + 2 with hMdef
  have hlog2x : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  have hM : 0 ≤ M := by rw [hMdef]; linarith
  have hpow : ∀ k : ℕ, (4/(4:ℝ)^k) * ((2:ℝ)^k + 1) = 4 * ((1/2:ℝ)^k + (1/4:ℝ)^k) := by
    intro k
    have h2 : (2:ℝ)^k / (4:ℝ)^k = (1/2:ℝ)^k := by
      rw [← div_pow]; norm_num
    have h4 : (1:ℝ) / (4:ℝ)^k = (1/4:ℝ)^k := by
      rw [show (1:ℝ) = 1^k by simp, ← div_pow]; norm_num
    have h4k : (4:ℝ)^k ≠ 0 := pow_ne_zero k (by norm_num)
    calc (4/(4:ℝ)^k) * ((2:ℝ)^k + 1)
        = 4 * ((2:ℝ)^k/(4:ℝ)^k) + 4 * ((1:ℝ)/(4:ℝ)^k) := by
          field_simp
      _ = 4 * ((1/2:ℝ)^k + (1/4:ℝ)^k) := by rw [h2, h4]; ring
  have hterm : ∀ k : ℕ,
      (4/(4:ℝ)^k) * (A * ((2:ℝ)^k + 1) * (Real.log (x + (2:ℝ)^k + 2) + L + 2))
        ≤ A * M * ((4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2)) := by
    intro k
    have hlog := log_add_pow_add_le x L hx hL k
    rw [← hMdef] at hlog
    have hcoef : (0:ℝ) ≤ A * (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) := by positivity
    calc (4/(4:ℝ)^k) * (A * ((2:ℝ)^k + 1) * (Real.log (x + (2:ℝ)^k + 2) + L + 2))
        = A * ((4/(4:ℝ)^k) * ((2:ℝ)^k + 1)) * (Real.log (x + (2:ℝ)^k + 2) + L + 2) := by ring
      _ = A * (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * (Real.log (x + (2:ℝ)^k + 2) + L + 2) := by
            rw [hpow]
      _ ≤ A * (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * (((k:ℝ) + 2) * M) :=
            mul_le_mul_of_nonneg_left hlog hcoef
      _ = A * M * ((4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2)) := by ring
  have hsum2 : ∑ k ∈ Finset.range (K+1), (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2) ≤ 48 := by
    have hsplit : ∑ k ∈ Finset.range (K+1), (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2)
        = 4 * (∑ k ∈ Finset.range (K+1), ((k:ℝ) + 2) * ((1/2:ℝ)^k))
          + 4 * (∑ k ∈ Finset.range (K+1), ((k:ℝ) + 2) * ((1/4:ℝ)^k)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _
      ring
    have h14 : ∑ k ∈ Finset.range (K+1), ((k:ℝ) + 2) * ((1/4:ℝ)^k)
        ≤ ∑ k ∈ Finset.range (K+1), ((k:ℝ) + 2) * ((1/2:ℝ)^k) := by
      apply Finset.sum_le_sum; intro k _
      have hle : ((1:ℝ)/4)^k ≤ ((1:ℝ)/2)^k := by
        apply pow_le_pow_left₀ (by norm_num) (by norm_num)
      have h2 : (0:ℝ) ≤ (k:ℝ) + 2 := by positivity
      nlinarith [hle, h2]
    have h12 := sum_kp2_half_le K
    rw [hsplit]
    linarith
  calc (∑ k ∈ Finset.range (K+1),
        (4/(4:ℝ)^k) * (A * ((2:ℝ)^k + 1) * (Real.log (x + (2:ℝ)^k + 2) + L + 2)))
      ≤ ∑ k ∈ Finset.range (K+1), A * M * ((4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2)) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = A * M * ∑ k ∈ Finset.range (K+1), (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2) := by
        rw [Finset.mul_sum]
    _ ≤ A * M * 48 := by
        apply mul_le_mul_of_nonneg_left hsum2
        positivity
    _ ≤ 50 * A * (L + Real.log (2 + x) + 2) := by
        rw [hMdef]
        nlinarith [hA, hlog2x, hL]

end Work.LinnikAreas.DhExplicit
