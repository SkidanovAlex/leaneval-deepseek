import Mathlib

namespace Work.ZeroDensity.Jutila

/-! ## Auxiliary arithmetic and summation lemmas -/

/-- The number of integers in `(N / 2^{j+1}, N / 2^j]` is controlled by the dyadic
scale: `N / 2^j ≤ 2 * (N / 2^{j+1}) + 1`. -/
lemma div_pow_le_two_mul_div_pow_succ_add_one (N j : ℕ) :
    N / 2^j ≤ 2 * (N / 2^(j+1)) + 1 := by
  have h1 : N / 2^(j+1) = (N / 2^j) / 2 := by
    rw [pow_succ]; exact (Nat.div_div_eq_div_mul N (2^j) 2).symm
  rw [h1]
  have hm : N / 2^j = 2 * (N / 2^j / 2) + (N / 2^j) % 2 := by
    conv_lhs => rw [← Nat.div_add_mod' (N/2^j) 2]
    ring
  have hlt : (N / 2^j) % 2 ≤ 1 := by
    have := Nat.mod_lt (N/2^j) (by norm_num : 0 < 2); omega
  omega

/-- **Harmonic mass of a full dyadic interval.** For any `a : ℕ`,
`Σ_{k = a+1}^{2a+1} 1/k ≤ 1`: the interval `(a, 2a+1]` has at most `a+1` terms, each at most
`1/(a+1)`. -/
lemma harmonicIntervalMass (a : ℕ) :
    (∑ k ∈ Finset.Icc (a+1) (2*a+1), (1 : ℝ) / (k : ℝ)) ≤ 1 := by
  have hterm : ∀ k ∈ Finset.Icc (a+1) (2*a+1), (1:ℝ)/(k:ℝ) ≤ 1/((a+1:ℕ):ℝ) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hpos : (0:ℝ) < ((a+1:ℕ):ℝ) := by positivity
    have hle : ((a+1:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
    exact one_div_le_one_div_of_le hpos hle
  have hcard : (Finset.Icc (a+1) (2*a+1)).card = a+1 := by rw [Nat.card_Icc]; omega
  calc (∑ k ∈ Finset.Icc (a+1) (2*a+1), (1:ℝ)/(k:ℝ))
      ≤ ∑ k ∈ Finset.Icc (a+1) (2*a+1), (1:ℝ)/((a+1:ℕ):ℝ) := Finset.sum_le_sum hterm
    _ = ((a+1:ℕ):ℝ) * (1/((a+1:ℕ):ℝ)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = 1 := by
        rw [mul_one_div]
        exact div_self (by positivity)

/-- **Harmonic mass of a dyadic fiber is at most `1`.**

For any `N j : ℕ`, the set of `k ∈ [1,N]` with `Nat.log 2 (N / k) = j` (i.e. the dyadic block
`N/2^{j+1} < k ≤ N/2^j`) has harmonic mass `Σ_{k in the block} 1/k ≤ 1`. -/
theorem harmonicFiberMass (N j : ℕ) :
    (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.log 2 (N / k) = j),
        (1 : ℝ) / (k : ℝ)) ≤ 1 := by
  have hsub : (Finset.Icc 1 N).filter (fun k => Nat.log 2 (N / k) = j)
      ⊆ Finset.Icc (N / 2^(j+1) + 1) (2*(N / 2^(j+1)) + 1) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hk2⟩, hlog⟩ := hk
    simp only [Finset.mem_Icc]
    have hkpos : 0 < k := by omega
    have hdiv1 : 1 ≤ N / k := by
      rw [Nat.le_div_iff_mul_le hkpos]; simpa using hk2
    have hne : N / k ≠ 0 := by omega
    have hiff := (Nat.log_eq_iff (Or.inr ⟨by norm_num, hne⟩)).1 hlog
    obtain ⟨hlo, hhi⟩ := hiff
    constructor
    · have hlt : N / 2^(j+1) < k := by
        rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^(j+1))]
        have h2 : N < 2^(j+1) * k := (Nat.div_lt_iff_lt_mul hkpos).1 hhi
        rwa [mul_comm] at h2
      omega
    · have hk_le : k ≤ N / 2^j := by
        rw [Nat.le_div_iff_mul_le (by positivity : 0 < 2^j)]
        calc k * 2^j = 2^j * k := by ring
          _ ≤ N := (Nat.le_div_iff_mul_le hkpos).1 hlo
      have harith := div_pow_le_two_mul_div_pow_succ_add_one N j
      omega
  calc (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.log 2 (N / k) = j), (1:ℝ)/(k:ℝ))
      ≤ ∑ k ∈ Finset.Icc (N / 2^(j+1) + 1) (2*(N / 2^(j+1)) + 1), (1:ℝ)/(k:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (by intro i hi hi'; exact one_div_nonneg.mpr (by positivity))
    _ ≤ 1 := harmonicIntervalMass (N / 2^(j+1))

end Work.ZeroDensity.Jutila
