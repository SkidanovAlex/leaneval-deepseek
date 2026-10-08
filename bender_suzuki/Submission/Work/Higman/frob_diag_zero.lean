/-
Copyright (c) 2024. All rights reserved.

# Linear independence of the Frobenius monomials `x ↦ x ^ (2 ^ (k + 1))`

In a finite field `F` of cardinality `2 ^ n` (necessarily of characteristic two),
the functions `x ↦ x ^ (2 ^ (k + 1))` for `k = 0, …, n - 1` are linearly
independent over `F`.  Equivalently, an identity

  `∑_{k < n} c k * x ^ (2 ^ (k + 1)) = 0`   (for every `x : F`)

forces every coefficient `c k` to vanish.

The key point is that on `F` one has `x ^ (2 ^ n) = x`, so the last term of the
sum reduces to the *linear* term `c (n - 1) * x`; the resulting polynomial
`∑_{k < n - 1} c k * X ^ (2 ^ (k + 1)) + c (n - 1) * X` has degree `< |F|` and
vanishes on all of `F`, hence is zero, and the monomials occurring in it have
pairwise distinct exponents `< |F|`.
-/

import Mathlib
import Submission.Work.Higman.QuadAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- In a finite field `F` with `Fintype.card F = 2 ^ n`, every element satisfies
`x ^ (2 ^ n) = x`. -/
lemma pow_two_pow_card {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (x : F) : x ^ (2 ^ n) = x := by
  rw [← hcard, FiniteField.pow_card]

/-- **Frobenius monomials are linearly independent.**  If `F` is a finite field with
`Fintype.card F = 2 ^ n`, `c : ℕ → F` and `∑_{k < n} c k * x ^ (2 ^ (k + 1)) = 0`
for every `x : F`, then `c k = 0` for every `k < n`. -/
theorem frob_diag_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (c : ℕ → F)
    (h : ∀ x : F, ∑ k ∈ Finset.range n, c k * x ^ (2 ^ (k + 1)) = 0) :
    ∀ k ∈ Finset.range n, c k = 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: the index range is empty.
    subst hn
    intro k hk
    exact absurd hk (Finset.notMem_empty k)
  -- Write `n = m + 1`; the top exponent `2 ^ (m + 1) = |F|` collapses to `x`.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- Exponent function: `k ↦ 2 ^ (k + 1)` for `k < m`, and `m ↦ 1`.
  refine monomial_indep_finset (Finset.range (m + 1))
    (fun k => if k < m then 2 ^ (k + 1) else 1) ?_ ?_ c ?_
  · -- Injectivity on `range (m + 1)`.
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    beta_reduce at hab
    by_cases ham : a < m
    · by_cases hbm : b < m
      · rw [ite_eq_left ham, ite_eq_left hbm] at hab
        have h2 : a + 1 = b + 1 := Nat.pow_right_injective (by norm_num) hab
        omega
      · rw [ite_eq_left ham, ite_eq_right hbm] at hab
        have hlt := Nat.one_lt_pow (by omega : a + 1 ≠ 0) (by norm_num : 1 < 2)
        omega
    · rw [ite_eq_right ham] at hab
      by_cases hbm : b < m
      · rw [ite_eq_left hbm] at hab
        have hlt := Nat.one_lt_pow (by omega : b + 1 ≠ 0) (by norm_num : 1 < 2)
        omega
      · rw [ite_eq_right hbm] at hab
        omega
  · -- Every exponent is `< |F| = 2 ^ (m + 1)`.
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [hcard]
    by_cases hkm : k < m
    · rw [ite_eq_left hkm]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · rw [ite_eq_right hkm]
      exact Nat.one_lt_pow (by omega : m + 1 ≠ 0) (by norm_num)
  · -- The pointwise relation, after collapsing the top term `x ^ (2 ^ (m + 1)) = x`.
    intro x
    rw [Finset.sum_range_succ]
    have hem : (if m < m then 2 ^ (m + 1) else 1) = 1 := by simp
    rw [hem, pow_one]
    have hcongr : ∀ k ∈ Finset.range m,
        c k * x ^ (if k < m then 2 ^ (k + 1) else 1) = c k * x ^ (2 ^ (k + 1)) := by
      intro k hk
      have : (if k < m then 2 ^ (k + 1) else 1) = 2 ^ (k + 1) := by
        rw [ite_eq_left (Finset.mem_range.mp hk)]
      rw [this]
    rw [Finset.sum_congr rfl hcongr]
    have hh := h x
    rw [Finset.sum_range_succ] at hh
    rw [pow_two_pow_card hcard x] at hh
    exact hh

end Work.Higman
