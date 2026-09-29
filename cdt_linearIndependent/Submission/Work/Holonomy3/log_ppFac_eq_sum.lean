import Mathlib
import Submission.Work.Holonomy3.log_den_defs

namespace Work.Holonomy3

/-- The `log` of the proper-prime-power factor `ppFac l n` is the sum of `log p` over all pairs
`(j, p)` with `j ≥ 2`, `p` prime, `l < p ^ j ≤ n`.  The outer range `Finset.Icc 2 n` may be
restricted to `Finset.Icc 2 (Nat.log 2 n)`: for `j > Nat.log 2 n` the inner filter is empty,
because `p` prime forces `p ≥ 2`, whence `p ^ j ≥ 2 ^ j > n`. -/
theorem log_ppFac_eq_sum (l n : ℕ) :
    Real.log ((Work.Holonomy3.ppFac l n : ℕ) : ℝ)
      = ∑ j ∈ Finset.Icc 2 (Nat.log 2 n),
          ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n),
            Real.log (p : ℝ) := by
  -- every `j` in `Icc 2 n` that is not in `Icc 2 (log 2 n)` gives an empty inner product
  have hinner_one : ∀ j ∈ Finset.Icc 2 n, j ∉ Finset.Icc 2 (Nat.log 2 n) →
      (∏ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n), (p : ℝ)) = 1 := by
    intro j hj hjnot
    rw [Finset.mem_Icc] at hj
    have hjgt : Nat.log 2 n < j := by
      by_contra hcon
      rw [not_lt] at hcon
      exact hjnot (Finset.mem_Icc.mpr ⟨hj.1, hcon⟩)
    refine Finset.prod_eq_one (fun p hp => ?_)
    exfalso
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨_, _⟩, hprime, _, hle⟩ := hp
    have h2 : 2 ≤ p := hprime.two_le
    have hlt : n < 2 ^ (Nat.log 2 n + 1) := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      simpa using h
    have hmono1 : 2 ^ (Nat.log 2 n + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmono2 : 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left h2 j
    omega
  -- unfold `ppFac` and push the `ℕ → ℝ` cast through the products
  have hcast : ((Work.Holonomy3.ppFac l n : ℕ) : ℝ)
      = ∏ j ∈ Finset.Icc 2 n,
          ∏ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n), (p : ℝ) := by
    simp only [Work.Holonomy3.ppFac, Nat.cast_prod]
  -- restrict the outer range from `Icc 2 n` to `Icc 2 (log 2 n)`
  have hrestrict :
      (∏ j ∈ Finset.Icc 2 n,
          ∏ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n), (p : ℝ))
        = ∏ j ∈ Finset.Icc 2 (Nat.log 2 n),
            ∏ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n), (p : ℝ) := by
    refine (Finset.prod_subset ?_ ?_).symm
    · intro x hx
      rw [Finset.mem_Icc] at hx ⊢
      exact ⟨hx.1, le_trans hx.2 (Nat.log_le_self 2 n)⟩
    · exact hinner_one
  rw [hcast, hrestrict, Real.log_prod]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.log_prod]
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos.ne'
  · intro j _
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      (show ((p : ℕ) : ℝ) ≠ 0 by exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos.ne'))

end Work.Holonomy3
