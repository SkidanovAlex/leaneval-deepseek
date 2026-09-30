import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.newton_series
import Submission.Work.N8.IntegralOnDilIff
import Submission.Work.N8.q0_arith_v2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Polynomial

/-- **Denominator of a coefficient.**  If `γ` has degree `≤ k` and is integral on `qℤ`, then
`k! q^k` clears the denominator of *every* coefficient of `γ`: there is `z : ℤ` with
`z = k! q^k · γ.coeff m`.

The `m`-th coefficient of the dilated polynomial `γ (q ·)` is `γ.coeff m · q^m`, and the Newton
series of `Work.N8.q0v2_fact_coeff_int` shows `k!` times it is an integer; multiplying by the
integer `q^(k-m)` produces `k! q^k γ.coeff m ∈ ℤ` (for `m ≤ k`; for `m > k` the coefficient
vanishes). -/
theorem coeff_mul_denom_int (k q : ℕ) {γ : Polynomial ℝ}
    (hdeg : γ.natDegree ≤ k) (hint : Work.BMF.IntegralOn (q : ℝ) γ) (m : ℕ) :
    ∃ z : ℤ, (z : ℝ) = ((k.factorial * q ^ k : ℕ) : ℝ) * γ.coeff m := by
  have hPint : Work.BMF.IntegralOn 1 (Work.BMF.dil (q : ℝ) γ) :=
    (Work.N8.IntegralOnDilIff q γ).mp hint
  have hPdeg : (Work.BMF.dil (q : ℝ) γ).natDegree ≤ k :=
    le_trans (Work.BMF.natDegree_dil_le _ _) hdeg
  obtain ⟨z, hz⟩ := q0v2_fact_coeff_int hPint hPdeg m
  rw [Work.BMF.coeff_dil] at hz
  by_cases hm : m ≤ k
  · refine ⟨(q : ℤ) ^ (k - m) * z, ?_⟩
    have hsplit : (q : ℝ) ^ k = (q : ℝ) ^ (k - m) * (q : ℝ) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hm]
    push_cast
    rw [← hz, hsplit]
    ring
  · have hγ0 : γ.coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (not_le.mp hm))
    exact ⟨0, by rw [hγ0, mul_zero, Int.cast_zero]⟩

theorem integral_coeff_denom (k q : ℕ) (hq : 1 ≤ q) {γ : Polynomial ℝ}
    (hdeg : γ.natDegree ≤ k) (hint : Work.BMF.IntegralOn (q : ℝ) γ) :
    ∃ c : ℕ → ℤ, γ = ∑ m ∈ Finset.range (k + 1),
      Polynomial.C ((c m : ℝ) / ((k.factorial * q ^ k : ℕ) : ℝ)) * Polynomial.X ^ m := by
  classical
  have hDpos : (0 : ℝ) < ((k.factorial * q ^ k : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos k) (pow_pos (by omega : 0 < q) k)
  have hD0 : ((k.factorial * q ^ k : ℕ) : ℝ) ≠ 0 := ne_of_gt hDpos
  have hz : ∀ m : ℕ, ∃ z : ℤ, (z : ℝ) = ((k.factorial * q ^ k : ℕ) : ℝ) * γ.coeff m :=
    fun m => coeff_mul_denom_int k q hdeg hint m
  choose c hc using hz
  refine ⟨c, ?_⟩
  apply Polynomial.ext
  intro n
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : n ≤ k
  · rw [Finset.sum_eq_single n]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      rw [eq_div_iff hD0, hc n, mul_comm]
    · intro b _ hbn
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hbn h.symm), mul_zero]
    · intro hnmem
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) hnmem
  · have hγ0 : γ.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (not_le.mp hn))
    rw [hγ0]
    symm
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmk : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    have hnm : n ≠ m := fun h => hn (h.symm ▸ hmk)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hnm, mul_zero]

end Work.N8
