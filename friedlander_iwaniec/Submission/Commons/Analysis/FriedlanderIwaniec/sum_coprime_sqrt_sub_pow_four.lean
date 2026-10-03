import Mathlib
import Submission.Commons.Analysis.FriedlanderIwaniec.sum_sqrt_sub_pow_four_sub_kappa_le
import Submission.Commons.NumberTheory.Totient.coprime_window_mainTerm_bound

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace Commons.Analysis.FriedlanderIwaniec

/-- **Abel summation (partial summation) bound.**

Let `a : ℕ → ℝ` be an arithmetic function whose partial sums from `0` are all
bounded by `D` in absolute value, and let `w : ℕ → ℝ` be non-increasing and
non-negative on `{0, …, N}`.  Then the weighted sum up to `N` is bounded by
`D · w 0`. -/
lemma abs_sum_range_mul_le_of_partial_sum_bound {a w : ℕ → ℝ} {D : ℝ} {N : ℕ}
    (hA : ∀ k, k ≤ N → |∑ c ∈ Finset.range (k + 1), a c| ≤ D)
    (hwmono : ∀ k, k < N → w (k + 1) ≤ w k)
    (hw0 : ∀ k, k ≤ N → 0 ≤ w k) :
    |∑ c ∈ Finset.range (N + 1), w c * a c| ≤ D * w 0 := by
  have hid : ∑ c ∈ Finset.range (N + 1), w c * a c
      = w N * (∑ c ∈ Finset.range (N + 1), a c)
        - ∑ i ∈ Finset.range N, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), a j) := by
    have h := Finset.sum_range_by_parts (R := ℝ) (M := ℝ) w a (N + 1)
    simpa only [smul_eq_mul, Nat.add_sub_cancel] using h
  have hDN : |∑ c ∈ Finset.range (N + 1), a c| ≤ D := hA N le_rfl
  have hwN0 : 0 ≤ w N := hw0 N le_rfl
  have hbnd1 : |w N * (∑ c ∈ Finset.range (N + 1), a c)| ≤ D * w N := by
    rw [abs_mul, abs_of_nonneg hwN0, mul_comm D]
    exact mul_le_mul_of_nonneg_left hDN hwN0
  have hbnd2 : |∑ i ∈ Finset.range N, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), a j)|
      ≤ D * (w 0 - w N) := by
    have hstep1 : |∑ i ∈ Finset.range N, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), a j)|
        ≤ ∑ i ∈ Finset.range N, |(w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), a j)| :=
      Finset.abs_sum_le_sum_abs _ _
    have hstep2 : ∑ i ∈ Finset.range N, |(w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), a j)|
        ≤ ∑ i ∈ Finset.range N, (w i - w (i + 1)) * D := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      have hle : w (i+1) ≤ w i := hwmono i hiN
      have hAi : |∑ j ∈ Finset.range (i + 1), a j| ≤ D := hA i (le_of_lt hiN)
      have hthis : |w (i + 1) - w i| = w i - w (i + 1) := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [abs_mul, hthis]
      exact mul_le_mul_of_nonneg_left hAi (by linarith)
    have hstep3 : ∑ i ∈ Finset.range N, (w i - w (i + 1)) * D = D * (w 0 - w N) := by
      rw [← Finset.sum_mul]
      have htel : ∑ i ∈ Finset.range N, (w i - w (i + 1)) = w 0 - w N := by
        have h2 : ∑ i ∈ Finset.range N, (w i - w (i+1))
            = - ∑ i ∈ Finset.range N, (w (i+1) - w i) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro i hi; ring
        rw [h2, Finset.sum_range_sub]; ring
      rw [htel]; ring
    linarith [hstep1, hstep2, hstep3]
  rw [hid]
  have hab : |w N * (∑ c ∈ Finset.range (N + 1), a c)
        - ∑ i ∈ Finset.range N, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), a j)|
      ≤ |w N * (∑ c ∈ Finset.range (N + 1), a c)|
        + |∑ i ∈ Finset.range N, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), a j)| := by
    simpa [sub_eq_add_neg] using abs_add_le (w N * (∑ c ∈ Finset.range (N + 1), a c))
      (-(∑ i ∈ Finset.range N, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), a j)))
  calc |w N * (∑ c ∈ Finset.range (N + 1), a c)
        - ∑ i ∈ Finset.range N, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), a j)|
      ≤ _ + _ := hab
    _ ≤ D * w N + D * (w 0 - w N) := add_le_add hbnd1 hbnd2
    _ = D * w 0 := by ring

/-- **Möbius discrepancy of the initial coprime window, partial sums.**

For `q ≥ 1` and every `N`, the partial sums of
`c ↦ [coprime c q] - φ(q)/q` over `c = 0, …, N` are bounded by
`d(q) + 1`, where `d(q)` is the number of divisors of `q`.  (The sharp bound
`d(q)` holds too; the extra `1` comes from the single term `c = 0`.) -/
lemma abs_sum_range_coprime_sub_ratio_le (q : ℕ) (hq : 1 ≤ q) (N : ℕ) :
    |∑ c ∈ Finset.range (N + 1), ((if Nat.Coprime c q then (1:ℝ) else 0)
        - (Nat.totient q : ℝ) / (q:ℝ))| ≤ ((Nat.divisors q).card : ℝ) + 1 := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hsplit : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hIccsum : ∑ c ∈ Finset.Icc 1 N, ((if Nat.Coprime c q then (1:ℝ) else 0)
        - (Nat.totient q : ℝ) / (q:ℝ))
      = (((Finset.Icc 1 N).filter (fun c => Nat.Coprime c q)).card : ℝ)
        - (N:ℝ) * ((Nat.totient q : ℝ) / (q:ℝ)) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_boole (fun c => Nat.Coprime c q) (Finset.Icc 1 N)
    · rw [Finset.sum_const]; simp
  have h0 : |(if Nat.Coprime 0 q then (1:ℝ) else 0) - (Nat.totient q : ℝ) / (q:ℝ)| ≤ 1 := by
    have hr0 : 0 ≤ (Nat.totient q : ℝ) / (q:ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hr1 : (Nat.totient q : ℝ) / (q:ℝ) ≤ 1 := by
      rw [div_le_one hqpos]; exact_mod_cast Nat.totient_le q
    rw [abs_le]
    constructor <;> split <;> norm_num at * <;> linarith
  have hN : |(((Finset.Icc 1 N).filter (fun c => Nat.Coprime c q)).card : ℝ)
        - (N:ℝ) * ((Nat.totient q : ℝ) / (q:ℝ))| ≤ ((Nat.divisors q).card : ℝ) := by
    have h := Commons.NumberTheory.Totient.coprime_window_mainTerm_bound N q hq
    have heq : (N:ℝ) * ((Nat.totient q : ℝ) / (q:ℝ))
        = (N:ℝ) * (Nat.totient q : ℝ) / (q:ℝ) := by ring
    rw [heq]; exact h
  rw [hsplit, Finset.sum_insert (by simp), hIccsum]
  calc |((if Nat.Coprime 0 q then (1:ℝ) else 0) - (Nat.totient q : ℝ) / (q:ℝ))
        + ((((Finset.Icc 1 N).filter (fun c => Nat.Coprime c q)).card : ℝ)
          - (N:ℝ) * ((Nat.totient q : ℝ) / (q:ℝ)))|
      ≤ |(if Nat.Coprime 0 q then (1:ℝ) else 0) - (Nat.totient q : ℝ) / (q:ℝ)|
        + |(((Finset.Icc 1 N).filter (fun c => Nat.Coprime c q)).card : ℝ)
          - (N:ℝ) * ((Nat.totient q : ℝ) / (q:ℝ))| := abs_add_le _ _
    _ ≤ 1 + ((Nat.divisors q).card : ℝ) := add_le_add h0 hN
    _ = ((Nat.divisors q).card : ℝ) + 1 := by ring

end Commons.Analysis.FriedlanderIwaniec
