
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Sum

open Polynomial
open scoped BigOperators

namespace Commons.Algebra.Binomial

/-- `tia_trunc n N` is the truncated binomial series `Σ_{k=0}^N (-1)^k C(n+k-1,k) X^k`. -/
noncomputable def tia_trunc (n N : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ))) * X ^ k

lemma tia_coeff_trunc (n N j : ℕ) (hj : j ≤ N) :
    (tia_trunc n N).coeff j = ((-1 : ℤ) ^ j * (Nat.choose (n + j - 1) j : ℤ)) := by
  unfold tia_trunc
  rw [finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hbj
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h; exact hbj h.symm
  · intro hjmem
    exfalso
    exact hjmem (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

lemma tia_coeff_trunc_gt (n N j : ℕ) (hj : N < j) :
    (tia_trunc n N).coeff j = 0 := by
  unfold tia_trunc
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Polynomial.coeff_C_mul_X_pow]
  have hjk : j ≠ k := by
    intro hjk
    have : k < j := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hj
    exact (Nat.ne_of_lt this) hjk.symm
  rw [if_neg hjk]

lemma tia_coeff_one_add_X_mul (p : ℤ[X]) (j : ℕ) :
    ((1 + X) * p).coeff j = p.coeff j + (if j = 0 then 0 else p.coeff (j - 1)) := by
  rw [add_mul, one_mul, coeff_add]
  by_cases hj : j = 0
  · subst j
    simp
  · have h1 : 1 ≤ j := by omega
    rw [← pow_one X]
    rw [Polynomial.coeff_X_pow_mul']
    rw [if_pos h1]
    simp [hj]

lemma tia_negOnePow_add_negOnePow_sub (j : ℕ) (hj : 1 ≤ j) :
    ((-1 : ℤ) ^ j + (-1 : ℤ) ^ (j - 1)) = 0 := by
  rcases j with _ | j
  · omega
  · change ((-1 : ℤ) ^ (j + 1) + (-1 : ℤ) ^ j) = 0
    rw [pow_succ']
    ring

lemma tia_coeff_trunc_one (N j : ℕ) : (tia_trunc 1 N).coeff j = if j ≤ N then (-1 : ℤ) ^ j else 0 := by
  by_cases hj : j ≤ N
  · rw [tia_coeff_trunc 1 N j hj]
    have : (Nat.choose (1 + j - 1) j : ℤ) = 1 := by
      congr 1
      have : 1 + j - 1 = j := by omega
      rw [this, Nat.choose_self]
    rw [this, mul_one]
    rw [if_pos hj]
  · rw [tia_coeff_trunc_gt 1 N j (by omega)]
    rw [if_neg hj]

/-- coefficient of the LHS of the base-case identity -/
lemma tia_coeff_one_add_X_mul_trunc_one (N j : ℕ) :
    ((1 + X) * tia_trunc 1 N).coeff j =
      (if j = 0 then (1 : ℤ) else 0) + (if j = N + 1 then (-1 : ℤ) ^ N else 0) := by
  rw [tia_coeff_one_add_X_mul]
  simp only [tia_coeff_trunc_one]
  by_cases h0 : j = 0
  · subst j
    simp
  · have h1 : 1 ≤ j := by omega
    by_cases hN : j ≤ N
    · simp [h0, hN]
      rw [if_pos (by omega : j ≤ N + 1)]
      rw [if_neg (by omega : j ≠ N + 1)]
      exact tia_negOnePow_add_negOnePow_sub j h1
    · by_cases hN1 : j = N + 1
      · subst j
        simp
      · simp [h0, hN, hN1]
        omega

/-- Base case n = 1 (geometric series). -/
lemma tia_base_one (N : ℕ) : (1 + X) * tia_trunc 1 N = 1 + Polynomial.C ((-1 : ℤ) ^ N) * X ^ (N + 1) := by
  ext j
  rw [tia_coeff_one_add_X_mul_trunc_one N j]
  rw [coeff_add, coeff_one, Polynomial.coeff_C_mul_X_pow]



/-- `(-1)^(j-1) = -(-1)^j` for `1 ≤ j`. -/
lemma tia_negOnePow_sub_one_eq_neg (j : ℕ) (hj : 1 ≤ j) :
    (-1 : ℤ) ^ (j - 1) = -((-1 : ℤ) ^ j) := by
  have h := tia_negOnePow_add_negOnePow_sub j hj
  linarith

/-- Pascal's triangle identity `C(n+j,j) = C(n+j-1,j-1) + C(n+j-1,j)` for `1 ≤ j`. -/
lemma tia_choose_pascal (n j : ℕ) (hj : 1 ≤ j) :
    (Nat.choose (n + j) j : ℤ) = (Nat.choose (n + j - 1) (j - 1) : ℤ) +
      (Nat.choose (n + j - 1) j : ℤ) := by
  have hnat : (n + j).choose j = (n + j - 1).choose (j - 1) + (n + j - 1).choose j := by
    calc
      (n + j).choose j = ((n + j - 1) + 1).choose ((j - 1) + 1) := by congr 1 <;> omega
      _ = (n + j - 1).choose (j - 1) + (n + j - 1).choose ((j - 1) + 1) := by
        exact Nat.choose_succ_succ' (n + j - 1) (j - 1)
      _ = (n + j - 1).choose (j - 1) + (n + j - 1).choose j := by
        congr 2
        omega
  exact_mod_cast hnat

/-- coefficient of `(1 + X) * tia_trunc (n+1) N`, in case `1 ≤ j ≤ N`. -/
lemma tia_coeff_one_add_X_mul_trunc_succ (n N j : ℕ) (h0 : j ≠ 0) (hN : j ≤ N) :
    ((1 + X) * tia_trunc (n + 1) N).coeff j =
      ((-1 : ℤ) ^ j * (Nat.choose (n + j - 1) j : ℤ)) := by
  rw [tia_coeff_one_add_X_mul]
  rw [if_neg h0]
  rw [tia_coeff_trunc (n + 1) N j hN, tia_coeff_trunc (n + 1) N (j - 1) (by omega)]
  rw [show ((n + 1) + j - 1) = n + j by omega]
  rw [show ((n + 1) + (j - 1) - 1) = n + j - 1 by omega]
  have hpascal := tia_choose_pascal n j (by omega : 1 ≤ j)
  -- a_j + a_{j-1} = (-1)^j (C(n+j,j) - C(n+j-1,j-1)) = (-1)^j C(n+j-1,j) = c_j
  calc
    ((-1 : ℤ) ^ j * (Nat.choose (n + j) j : ℤ)) +
        ((-1 : ℤ) ^ (j - 1) * (Nat.choose (n + j - 1) (j - 1) : ℤ))
        = ((-1 : ℤ) ^ j * ((Nat.choose (n + j) j : ℤ) - (Nat.choose (n + j - 1) (j - 1) : ℤ))) := by
          rw [tia_negOnePow_sub_one_eq_neg j (by omega : 1 ≤ j)]
          ring
    _ = ((-1 : ℤ) ^ j * (Nat.choose (n + j - 1) j : ℤ)) := by
          rw [hpascal]
          ring



/-- The step identity: multiplying by `(1+X)` shifts the series from `n+1` to `n`. -/
lemma tia_link (n N : ℕ) :
    (1 + X) * tia_trunc (n + 1) N =
      tia_trunc n N + Polynomial.C (((-1 : ℤ) ^ N * (Nat.choose (n + N) N : ℤ))) * X ^ (N + 1) := by
  ext j
  by_cases h0 : j = 0
  · subst j
    rw [tia_coeff_one_add_X_mul]
    rw [tia_coeff_trunc (n + 1) N 0 (by omega)]
    rw [coeff_add, tia_coeff_trunc n N 0 (by omega), Polynomial.coeff_C_mul_X_pow]
    simp
  · have h1 : 1 ≤ j := by omega
    by_cases hN : j ≤ N
    · rw [tia_coeff_one_add_X_mul_trunc_succ n N j h0 hN]
      rw [coeff_add, tia_coeff_trunc n N j hN, Polynomial.coeff_C_mul_X_pow]
      rw [if_neg (by omega : j ≠ N + 1)]
      simp
    · have hNlt : N < j := by omega
      by_cases hN1 : j = N + 1
      · subst j
        rw [tia_coeff_one_add_X_mul]
        rw [if_neg (by omega : N + 1 ≠ 0)]
        rw [tia_coeff_trunc_gt (n + 1) N (N + 1) (by omega)]
        rw [show N + 1 - 1 = N by omega]
        rw [tia_coeff_trunc (n + 1) N N (by omega)]
        rw [coeff_add, tia_coeff_trunc_gt n N (N + 1) (by omega), Polynomial.coeff_C_mul_X_pow]
        rw [if_pos rfl]
        rw [show ((n + 1) + N - 1) = n + N by omega]
      · rw [tia_coeff_one_add_X_mul]
        rw [if_neg h0]
        rw [tia_coeff_trunc_gt (n + 1) N j hNlt, tia_coeff_trunc_gt (n + 1) N (j - 1) (by omega)]
        rw [coeff_add, tia_coeff_trunc_gt n N j hNlt, Polynomial.coeff_C_mul_X_pow]
        rw [if_neg hN1]

/-- Main recursive construction (theorem body, for any fixed `N`). -/
lemma tia_exists_R (n N : ℕ) (hn : 1 ≤ n) :
    ∃ R : ℤ[X], (1 + X) ^ n * tia_trunc n N = 1 + X ^ (N + 1) * R := by
  have main : ∀ n : ℕ, 1 ≤ n → ∃ R : ℤ[X], (1 + X) ^ n * tia_trunc n N = 1 + X ^ (N + 1) * R := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
        intro h1
        by_cases hn0 : n = 0
        · subst n
          refine ⟨Polynomial.C ((-1 : ℤ) ^ N), ?_⟩
          simp
          rw [tia_base_one]
          simp [mul_comm]
        · have hn : 1 ≤ n := by omega
          obtain ⟨R1, hR1⟩ := ih hn
          refine ⟨R1 + Polynomial.C (((-1 : ℤ) ^ N * (Nat.choose (n + N) N : ℤ))) * (1 + X) ^ n, ?_⟩
          calc
            (1 + X) ^ (n + 1) * tia_trunc (n + 1) N
                = (1 + X) ^ n * ((1 + X) * tia_trunc (n + 1) N) := by
                  rw [pow_succ']
                  ring
            _ = (1 + X) ^ n * (tia_trunc n N +
                  Polynomial.C (((-1 : ℤ) ^ N * (Nat.choose (n + N) N : ℤ))) * X ^ (N + 1)) := by
                  rw [tia_link]
            _ = (1 + X) ^ n * tia_trunc n N +
                  X ^ (N + 1) * (Polynomial.C (((-1 : ℤ) ^ N * (Nat.choose (n + N) N : ℤ))) * (1 + X) ^ n) := by
                  ring
            _ = (1 + X ^ (N + 1) * R1) +
                  X ^ (N + 1) * (Polynomial.C (((-1 : ℤ) ^ N * (Nat.choose (n + N) N : ℤ))) * (1 + X) ^ n) := by
                  rw [hR1]
            _ = 1 + X ^ (N + 1) *
                  (R1 + Polynomial.C (((-1 : ℤ) ^ N * (Nat.choose (n + N) N : ℤ))) * (1 + X) ^ n) := by
                  ring
  exact main n hn



/-- The truncated binomial inverse identity:
`(1+X)^n · Σ_{k=0}^{N} (-1)^k C(n+k-1,k) X^k ≡ 1 (mod X^(N+1))`. -/
theorem trunc_inv_add_one (n N : ℕ) (hn : 1 ≤ n) :
    ∃ R : ℤ[X],
      (1 + X) ^ n *
          (∑ k ∈ Finset.range (N + 1),
            Polynomial.C (((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ))) * X ^ k) =
        1 + X ^ (N + 1) * R := by
  change ∃ R : ℤ[X], (1 + X) ^ n * tia_trunc n N = 1 + X ^ (N + 1) * R
  exact tia_exists_R n N hn

end Commons.Algebra.Binomial
