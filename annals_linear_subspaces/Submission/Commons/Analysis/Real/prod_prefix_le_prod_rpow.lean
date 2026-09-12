import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

/-- Auxiliary combinatorial inequality: if `b` is nondecreasing between the first `k`
indices and the tail `[k, d)`, then `d * ∑_{i<k} b i ≤ k * ∑_{i<d} b i`, i.e. the
average of the first `k` terms is at most the average of all `d` terms. -/
private lemma sum_range_mul_le_of_tail {k d : ℕ} (hk : k ≤ d) {b : ℕ → ℝ}
    (hb : ∀ i j, i < k → k ≤ j → j < d → b i ≤ b j) :
    (d : ℝ) * (∑ i ∈ Finset.range k, b i) ≤
      (k : ℝ) * (∑ i ∈ Finset.range d, b i) := by
  induction d with
  | zero =>
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    simp
  | succ d ih =>
    by_cases hkd : k ≤ d
    · have hIH := ih hkd (fun i j hi hj hj' => hb i j hi hj (Nat.lt_succ_of_lt hj'))
      have hS : (∑ i ∈ Finset.range k, b i) ≤ (k : ℝ) * b d := by
        calc ∑ i ∈ Finset.range k, b i
            ≤ ∑ _i ∈ Finset.range k, b d :=
              Finset.sum_le_sum (fun i hi =>
                hb i d (Finset.mem_range.mp hi) hkd (Nat.lt_succ_self d))
          _ = (k : ℝ) * b d := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith [hIH, hS]
    · have hk' : k = d + 1 := le_antisymm hk (Nat.succ_le_of_lt (Nat.lt_of_not_le hkd))
      subst hk'
      simp

theorem prod_prefix_le_prod_rpow {d k : ℕ} (hd : 0 < d) (hk : k ≤ d) {lam : ℕ → ℝ}
    (hpos : ∀ i, 0 < i → i ≤ d → 0 < lam i) (hmono : Monotone lam) :
    Finset.prod (Finset.range k) (fun i => lam (i + 1)) ≤
      (Finset.prod (Finset.range d) (fun i => lam (i + 1))) ^ ((k : ℝ) / (d : ℝ)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpos' : ∀ i, i < d → 0 < lam (i + 1) :=
    fun i hi => hpos (i + 1) (Nat.succ_pos i) (by omega)
  have hb : ∀ i j, i < k → k ≤ j → j < d →
      Real.log (lam (i + 1)) ≤ Real.log (lam (j + 1)) := by
    intro i j hi hj hj'
    exact Real.log_le_log (hpos' i (by omega)) (hmono (by omega))
  have hkey := sum_range_mul_le_of_tail hk hb
  have hdiv : (∑ i ∈ Finset.range k, Real.log (lam (i + 1))) ≤
      ((k : ℝ) / (d : ℝ)) * (∑ i ∈ Finset.range d, Real.log (lam (i + 1))) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdR]
    linarith [hkey]
  have hApos : 0 < ∏ i ∈ Finset.range k, lam (i + 1) :=
    Finset.prod_pos (fun i hi => hpos' i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))
  have hPpos : 0 < ∏ i ∈ Finset.range d, lam (i + 1) :=
    Finset.prod_pos (fun i hi => hpos' i (Finset.mem_range.mp hi))
  refine (Real.log_le_log_iff hApos (Real.rpow_pos_of_pos hPpos _)).mp ?_
  rw [Real.log_prod (fun i hi =>
        ne_of_gt (hpos' i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))),
      Real.log_rpow hPpos,
      Real.log_prod (fun i hi => ne_of_gt (hpos' i (Finset.mem_range.mp hi)))]
  exact hdiv

end Commons.Analysis.Real