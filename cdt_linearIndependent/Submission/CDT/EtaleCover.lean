/-
# Lemma `etalecover` of Calegari–Dimitrov–Tang: the symmetrisation of denominator types

This module formalises the *integrality* content of the paper's Lemma `etalecover`
(arXiv:2408.15403, §"The relationship between `Y(2)` and `Y₀(2)`"), the input which the paper uses
for the denominator types of `B₄` and `B₇`.

Setting `y = x + x/(x-1) = x²/(x-1)`, the paper considers the polynomials
`P_n(y) := x^n + (x/(x-1))^n` (`n ≥ 0`), which are integral, satisfy `P_0 = 2`, `P_1 = y` and the
recurrence `P_{n+2} = y·P_{n+1} − y·P_n`, and whose `y`-support lies in the degree range
`[⌈n/2⌉, n]`.  Consequently, if a power series `f(x) = Σ A_n x^n` has *denominator type*
`[1,…,c·n]` (i.e. `A_n · lcmUpto (c·n) ∈ ℤ`), then the symmetrised series

`2F(y) = f(x) + f(x/(x-1)) = Σ_k A_k P_k(y) =: Σ_n B_n y^n`

has denominator type `[1,…,2c·n]` (i.e. `B_n · lcmUpto (2c·n) ∈ ℤ`).

The reason is the paper's: `P_k` contributes to `y^n` only for `k ∈ [n, 2n]`, and the `lcm`-windows
are nested, `lcmUpto (c·k) ∣ lcmUpto (2c·n)` for `k ≤ 2n`.

Everything here is at the level of sequences (`A`, `B`) and polynomials — no power series are
needed. -/

import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.lcmUpto_dvd_of_le

open Polynomial Finset
open scoped BigOperators

namespace Submission.CDT.EtaleCover

/-- The pair of consecutive polynomials `(P_n, P_{n+1})` of the paper, defined recursively by
`P_0 = 2`, `P_1 = y` and `P_{n+2} = y·P_{n+1} − y·P_n`. -/
noncomputable def symAux : ℕ → Polynomial ℚ × Polynomial ℚ
  | 0 => (2, Polynomial.X)
  | (n+1) => ((symAux n).2, Polynomial.X * (symAux n).2 - Polynomial.X * (symAux n).1)

/-- `P_n(y) = x^n + (x/(x−1))^n` as a polynomial in `y`, via the recurrence. -/
noncomputable def symPoly (n : ℕ) : Polynomial ℚ := (symAux n).1

@[simp] theorem symPoly_zero : symPoly 0 = 2 := rfl

@[simp] theorem symPoly_one : symPoly 1 = Polynomial.X := rfl

theorem symPoly_succ_succ (n : ℕ) :
    symPoly (n + 2) = Polynomial.X * symPoly (n + 1) - Polynomial.X * symPoly n := rfl

theorem symPoly_eq_snd_succ (n : ℕ) : symPoly (n + 1) = (symAux n).2 := rfl

/-- Coefficient of `X * p` at `0` vanishes. -/
theorem coeff_X_mul_zero {R : Type*} [Semiring R] (p : R[X]) : (Polynomial.X * p).coeff 0 = 0 :=
  Polynomial.X_dvd_iff.mp (dvd_mul_right Polynomial.X p)

/-- The coefficients of `P_n` are integers. -/
theorem symPoly_coeff_int (n m : ℕ) : ∃ w : ℤ, (symPoly n).coeff m = (w : ℚ) := by
  revert m
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · rw [symPoly_zero]
        by_cases hm : m = 0
        · subst hm; exact ⟨2, by norm_num⟩
        · refine ⟨0, ?_⟩
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [Polynomial.natDegree_ofNat]; omega)]
          norm_num
      · rw [symPoly_one, Polynomial.coeff_X]
        refine ⟨if 1 = m then 1 else 0, ?_⟩
        split <;> simp
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      rw [symPoly_succ_succ, Polynomial.coeff_sub]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [coeff_X_mul_zero, coeff_X_mul_zero, sub_zero]
        exact ⟨0, by simp⟩
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul]
        obtain ⟨w1, h1⟩ := ih (k+1) (by omega) m'
        obtain ⟨w2, h2⟩ := ih k (by omega) m'
        exact ⟨w1 - w2, by rw [h1, h2]; push_cast; ring⟩

/-- **The support of `P_n`**: its `y`-coefficients vanish outside the degree range `[⌈n/2⌉, n]`
(in the form `2m < n`, resp. `n < m`). -/
theorem symPoly_coeff_eq_zero (n m : ℕ) (h : 2 * m < n ∨ n < m) : (symPoly n).coeff m = 0 := by
  revert m h
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m h
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · rw [symPoly_zero]
        rcases h with h | h
        · omega
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [Polynomial.natDegree_ofNat]; omega)
      · rw [symPoly_one, Polynomial.coeff_X]
        rcases h with h | h
        · have hm0 : m = 0 := by omega
          subst hm0
          norm_num
        · simp [show ¬ (1 = m) by omega]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      rw [symPoly_succ_succ, Polynomial.coeff_sub]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [coeff_X_mul_zero, coeff_X_mul_zero, sub_zero]
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul]
        rcases h with h | h
        · rw [ih (k+1) (by omega) m' (Or.inl (by omega)),
            ih k (by omega) m' (Or.inl (by omega)), sub_zero]
        · rw [ih (k+1) (by omega) m' (Or.inr (by omega)),
            ih k (by omega) m' (Or.inr (by omega)), sub_zero]

/-- The coefficient index `k` of a nonvanishing coefficient of `P_k` at `n` lies in `[n, 2n]`. -/
theorem symPoly_coeff_eq_zero_of_not_mem {n k : ℕ} (h : k ∉ Finset.Icc n (2 * n)) :
    (symPoly k).coeff n = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact symPoly_coeff_eq_zero k n (Or.inr h)
  · exact symPoly_coeff_eq_zero k n (Or.inl h)

/-- **The integrality part of Lemma `etalecover`.**  If `A_n · lcmUpto (c·n) ∈ ℤ` for all `n`, then
the coefficient `B_n = Σ_{k} A_k · [y^n]P_k` of the symmetrisation satisfies
`B_n · lcmUpto (2c·n) ∈ ℤ`. -/
theorem etalecover_integrality (c : ℕ) (A : ℕ → ℚ)
    (hA : ∀ k, ∃ z : ℤ, (Nat.lcmUpto (c * k) : ℚ) * A k = (z : ℚ)) (n : ℕ) :
    ∃ z : ℤ, (Nat.lcmUpto (2 * c * n) : ℚ) *
      (∑ k ∈ Finset.Icc n (2 * n), A k * ((symPoly k).coeff n : ℚ)) = (z : ℚ) := by
  classical
  have hterm : ∀ k : ℕ, ∃ z : ℤ, k ∈ Finset.Icc n (2 * n) →
      (Nat.lcmUpto (2 * c * n) : ℚ) * (A k * ((symPoly k).coeff n : ℚ)) = (z : ℚ) := by
    intro k
    by_cases hk : k ∈ Finset.Icc n (2 * n)
    · obtain ⟨z, hz⟩ := hA k
      obtain ⟨w, hw⟩ := symPoly_coeff_int k n
      have hkn : k ≤ 2 * n := (Finset.mem_Icc.mp hk).2
      have hdvd : Nat.lcmUpto (c * k) ∣ Nat.lcmUpto (2 * c * n) := by
        refine Commons.NumberTheory.Chebyshev.lcmUpto_dvd_of_le ?_
        calc c * k ≤ c * (2 * n) := Nat.mul_le_mul_left c hkn
          _ = 2 * c * n := by ring
      have hsplit : (Nat.lcmUpto (2 * c * n) : ℚ) = (Nat.lcmUpto (c * k) : ℚ)
          * ((Nat.lcmUpto (2 * c * n) / Nat.lcmUpto (c * k) : ℕ) : ℚ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      refine ⟨z * w * ((Nat.lcmUpto (2 * c * n) / Nat.lcmUpto (c * k) : ℕ) : ℤ),
        fun _ => ?_⟩
      rw [hsplit, hw]
      have hre : (Nat.lcmUpto (c * k) : ℚ)
            * ((Nat.lcmUpto (2 * c * n) / Nat.lcmUpto (c * k) : ℕ) : ℚ) * (A k * (w : ℚ))
          = ((Nat.lcmUpto (c * k) : ℚ) * A k)
            * (((Nat.lcmUpto (2 * c * n) / Nat.lcmUpto (c * k) : ℕ) : ℚ) * (w : ℚ)) := by
        ring
      rw [hre, hz, Int.cast_mul, Int.cast_mul, Int.cast_natCast]
      ring
    · exact ⟨0, fun h => absurd h hk⟩
  choose F hF using hterm
  refine ⟨∑ k ∈ Finset.Icc n (2 * n), F k, ?_⟩
  rw [Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun k hk => hF k hk

end Submission.CDT.EtaleCover
