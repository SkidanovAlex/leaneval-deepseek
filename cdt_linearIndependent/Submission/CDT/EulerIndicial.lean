import Mathlib
import Submission.CDT.RatFuncOrder
import Submission.CDT.RatFuncDeriv
import Submission.Commons.Algebra.Polynomial.eulerOperator_factor

/-!
# The Euler-operator (Frobenius) cascade

For a rational function `f = p/q` and a linear factor `z = X - C α`, the
quantity `z^j f^{(j)}` differs from `(N)_j f` (where `N = ord_α f` and `(N)_j`
is the falling factorial) by a rational function of strictly larger order at
`α`.  This is the formal-power-series statement

  `z^j f^{(j)} = (N)_j f + (higher order at α)`,

which is the engine of the Frobenius/indicial analysis: summing with
coefficients `B_j` that are *regular* at `α` turns `∑ B_j z^j f^{(j)}` into
`(∑ (N)_j B_j(α)) f` plus higher-order terms.

Here `f^{(j)}` is written out as `C_j / q^{j+1}` with `C_j` the recursive
"numerator of the `j`-th derivative" (`C_0 = p`, `C_{j+1} = C_j'q - (j+1)C_jq'`),
so that the whole argument is polynomial divisibility and no Laurent expansion
is required.  The central estimate is `dnum_sub_dvd`:
`z^{a + jb + 1} ∣ z^j C_j - (N)_j p q^j` (with `a = rm_α p`, `b = rm_α q`).
-/

noncomputable section

namespace Submission.CDT

open Polynomial

set_option linter.unusedSimpArgs false

variable {K : Type*} [Field K]

/-- The falling factorial `(N)_j = N (N-1) ⋯ (N-j+1)` as an integer. -/
def fallFact (N : ℤ) (j : ℕ) : ℤ := (Finset.range j).prod (fun i => N - (i : ℤ))

@[simp] lemma fallFact_zero (N : ℤ) : fallFact N 0 = 1 := by simp [fallFact]

lemma fallFact_succ (N : ℤ) (j : ℕ) : fallFact N (j + 1) = fallFact N j * (N - j) := by
  simp [fallFact, Finset.prod_range_succ]

/-- The numerator of the `j`-th derivative of `p/q`: `f^{(j)} = C_j / q^{j+1}`. -/
def dnum (p q : Polynomial K) : ℕ → Polynomial K
  | 0 => p
  | (j + 1) => (dnum p q j).derivative * q
      - Polynomial.C (((j : ℕ) + 1 : ℕ) : K) * (dnum p q j * q.derivative)

lemma dnum_succ (p q : Polynomial K) (j : ℕ) :
    dnum p q (j + 1) = (dnum p q j).derivative * q
      - Polynomial.C (((j : ℕ) + 1 : ℕ) : K) * (dnum p q j * q.derivative) := rfl

/-- `f^{(j)} = C_j/q^{j+1}` for `f = p/q`. -/
theorem dRat_iterate_dnum (p q : Polynomial K) (hq : q ≠ 0) (j : ℕ) :
    (dRat^[j] (algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q))
      = algebraMap (Polynomial K) (RatFunc K) (dnum p q j)
        / (algebraMap (Polynomial K) (RatFunc K) q) ^ (j + 1) := by
  induction j with
  | zero => simp [dnum]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, ← map_pow, dRat_div]
      have hAq : algebraMap (Polynomial K) (RatFunc K) q ≠ 0 := by simpa using hq
      have hq' : (q ^ (k + 1)).derivative
          = Polynomial.C (((k : ℕ) + 1 : ℕ) : K) * (q ^ k * q.derivative) := by
        rw [Polynomial.derivative_pow, show k + 1 - 1 = k from by omega]
        ring
      rw [hq', dnum_succ]
      simp only [map_mul, map_pow, map_add, map_sub, map_one]
      field_simp [hAq]
      ring

/-- `D_j = z^j C_j - F_j · p q^j`, with `F` the falling factorials of `N`
carried as an explicit sequence of polynomial constants. -/
def DbN (z p q : Polynomial K) (F : ℕ → Polynomial K) (j : ℕ) : Polynomial K :=
  z ^ j * dnum p q j - F j * (p * q ^ j)

/-- **The Euler cascade recursion.**  `D_{j+1}` is an explicit combination of
`D_j` and of the Euler expression `z(p'q - pq') - Npq`. -/
theorem DbN_rec (z : Polynomial K) (hz : z.derivative = 1) (p q : Polynomial K)
    (N : Polynomial K) (F : ℕ → Polynomial K) (hF0 : F 0 = 1)
    (hFc : ∀ j, (F j).derivative = 0)
    (hF : ∀ j, F (j + 1) = F j * (N - (j : Polynomial K))) (j : ℕ) :
    DbN z p q F (j + 1)
      = F j * q ^ j * (z * (p.derivative * q - p * q.derivative) - N * (p * q))
        + z * (DbN z p q F j).derivative * q
        - ((j : Polynomial K) + 1) * z * (DbN z p q F j) * q.derivative
        - (j : Polynomial K) * (DbN z p q F j) * q := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [DbN]
    rw [hF0, hF 0]
    simp only [dnum, hz, hF0, Polynomial.C_eq_natCast, Polynomial.C_eq_intCast,
      Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_pow, Polynomial.derivative_one,
      Polynomial.derivative_X, mul_one, mul_zero, sub_zero, zero_mul, sub_self]
    push_cast
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp only [DbN]
    rw [hF (m + 1)]
    simp only [dnum, hz, hFc, Polynomial.C_eq_natCast, Polynomial.C_eq_intCast,
      Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_pow, Polynomial.derivative_one,
      Polynomial.derivative_X, Polynomial.derivative_natCast,
      mul_one, mul_zero, sub_zero, zero_mul, sub_self]
    push_cast
    ring

end Submission.CDT
