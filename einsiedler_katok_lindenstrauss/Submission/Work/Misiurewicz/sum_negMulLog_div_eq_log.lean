import Mathlib

namespace Work.Misiurewicz

theorem sum_negMulLog_div_eq_log {ι : Type*} [Fintype ι] (m : ι → ℕ) (n : ℕ)
    (hm : ∀ i, m i ≤ 1) (hcard : (Finset.univ.filter (fun i => 1 ≤ m i)).card = n) :
    ∑ i, Real.negMulLog ((m i : ℝ) / (n : ℝ)) = Real.log (n : ℝ) := by
  -- scalar identity, including the degenerate case `n = 0`
  have hkey : (n : ℝ) * Real.negMulLog (1 / (n : ℝ)) = Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [Real.negMulLog]
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [Real.negMulLog, Real.log_div one_ne_zero hn', Real.log_one, zero_sub]
      field_simp
  set s := Finset.univ.filter (fun i => 1 ≤ m i) with hs
  have hscard : s.card = n := by rw [hs]; exact hcard
  -- every `i` with `m i ≠ 1` contributes `0`
  have hzero : ∀ i, i ∉ s → Real.negMulLog ((m i : ℝ) / (n : ℝ)) = 0 := by
    intro i hi
    have hmi : m i ≤ 1 := hm i
    have h1 : ¬ 1 ≤ m i := by rw [hs] at hi; simpa using hi
    have hm0 : m i = 0 := by omega
    rw [hm0]
    simp [Real.negMulLog]
  -- every `i ∈ s` contributes `negMulLog (1/n)`
  have hone : ∀ i, i ∈ s →
      Real.negMulLog ((m i : ℝ) / (n : ℝ)) = Real.negMulLog (1 / (n : ℝ)) := by
    intro i hi
    have hmi : m i ≤ 1 := hm i
    have h1 : 1 ≤ m i := by rw [hs] at hi; simpa using hi
    have hm1 : m i = 1 := by omega
    rw [hm1]
    norm_num
  calc ∑ i, Real.negMulLog ((m i : ℝ) / (n : ℝ))
      = ∑ i ∈ s, Real.negMulLog ((m i : ℝ) / (n : ℝ)) := by
          rw [Finset.sum_subset (Finset.subset_univ s) (fun x _ hx => hzero x hx)]
    _ = ∑ i ∈ s, Real.negMulLog (1 / (n : ℝ)) :=
          Finset.sum_congr rfl (fun i hi => hone i hi)
    _ = s.card • Real.negMulLog (1 / (n : ℝ)) := Finset.sum_const _
    _ = n • Real.negMulLog (1 / (n : ℝ)) := by rw [hscard]
    _ = Real.log (n : ℝ) := by rw [nsmul_eq_mul]; exact hkey

end Work.Misiurewicz
