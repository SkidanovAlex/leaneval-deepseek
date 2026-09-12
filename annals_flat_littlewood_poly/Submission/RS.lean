import Mathlib

/-! Rudin-Shapiro polynomials, following Section 3 of Balister--Bollobas--Morris--
Sahasrabudhe--Tiba, "Flat Littlewood polynomials exist", Ann. of Math. 192 (2020). -/

noncomputable section

open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission

namespace RudinShapiro

/-- The Rudin-Shapiro pair `(P_t, Q_t)`: `P_{t+1} = P_t + X^(2^t) Q_t`,
`Q_{t+1} = P_t - X^(2^t) Q_t`, `P_0 = Q_0 = 1`. -/
def pair : ℕ → ℂ[X] × ℂ[X]
  | 0 => (1, 1)
  | t + 1 =>
      let (p, q) := pair t
      (p + X ^ 2 ^ t * q, p - X ^ 2 ^ t * q)

/-- The first Rudin-Shapiro polynomial of level `t`. -/
def P (t : ℕ) : ℂ[X] := (pair t).1

/-- The second Rudin-Shapiro polynomial of level `t`. -/
def Q (t : ℕ) : ℂ[X] := (pair t).2

@[simp] lemma P_zero : P 0 = 1 := rfl
@[simp] lemma Q_zero : Q 0 = 1 := rfl

@[simp] lemma P_succ (t : ℕ) : P (t + 1) = P t + X ^ 2 ^ t * Q t := by
  cases t <;> simp [P, Q, pair]
@[simp] lemma Q_succ (t : ℕ) : Q (t + 1) = P t - X ^ 2 ^ t * Q t := by
  cases t <;> simp [P, Q, pair]

lemma eval_P_succ (t : ℕ) (z : ℂ) : (P (t + 1)).eval z = (P t).eval z + z ^ 2 ^ t * (Q t).eval z := by
  rw [P_succ]; simp
lemma eval_Q_succ (t : ℕ) (z : ℂ) : (Q (t + 1)).eval z = (P t).eval z - z ^ 2 ^ t * (Q t).eval z := by
  rw [Q_succ]; simp

lemma pow_two_succ (t : ℕ) : 2 ^ (t + 1) = 2 * 2 ^ t := by
  rw [pow_succ, mul_comm]

lemma two_pow_pos (t : ℕ) : 0 < 2 ^ t := pow_pos (by norm_num) t
lemma two_pow_ge_one (t : ℕ) : 1 ≤ 2 ^ t := by
  have hp : 2 ^ 0 ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Nat.zero_le t)
  simpa using hp

/-- For `i < 2 ^ t`, the coefficient of `X^(2^t) * q` at `i` vanishes. -/
lemma coeff_X_pow_mul_of_lt {q : ℂ[X]} (t i : ℕ) (hi : i < 2 ^ t) :
    (X ^ 2 ^ t * q).coeff i = 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hx1 : x.1 + x.2 = i := by simpa using hx
  have hxlt : x.1 < 2 ^ t := lt_of_le_of_lt (Nat.le.intro hx1) hi
  have : x.1 ≠ 2 ^ t := ne_of_lt hxlt
  simp [Polynomial.coeff_X_pow, this]

/-- `P` is a prefix of `P (t+1)` below degree `2^t`. -/
lemma coeff_P_extend (t i : ℕ) (hi : i < 2 ^ t) : (P (t + 1)).coeff i = (P t).coeff i := by
  rw [P_succ, Polynomial.coeff_add, coeff_X_pow_mul_of_lt t i hi]
  simp

/-- For `i < 2^t`, the coefficient of `Q (t+1)` at `i` equals the coefficient of `P t` at `i`. -/
lemma coeff_Q_extend (t i : ℕ) (hi : i < 2 ^ t) : (Q (t + 1)).coeff i = (P t).coeff i := by
  rw [Q_succ, Polynomial.coeff_sub, coeff_X_pow_mul_of_lt t i hi]
  simp

/-- The top half of `P (t+1)` (indices `2^t + j`) consists of the coefficients of `Q t`. -/
lemma P_Q_bounds (t : ℕ) :
    (P t).natDegree ≤ 2 ^ t - 1 ∧ (Q t).natDegree ≤ 2 ^ t - 1 ∧
    (∀ i, i < 2 ^ t → (P t).coeff i = 1 ∨ (P t).coeff i = -1) ∧
    (∀ i, i < 2 ^ t → (Q t).coeff i = 1 ∨ (Q t).coeff i = -1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h2t : (1 : ℕ) ≤ 2 ^ t := two_pow_ge_one t
      have hdegP : (P t).natDegree ≤ 2 ^ t - 1 := ih.1
      have hdegQ : (Q t).natDegree ≤ 2 ^ t - 1 := ih.2.1
      have hcP : ∀ i, i < 2 ^ t → (P t).coeff i = 1 ∨ (P t).coeff i = -1 := ih.2.2.1
      have hcQ : ∀ i, i < 2 ^ t → (Q t).coeff i = 1 ∨ (Q t).coeff i = -1 := ih.2.2.2
      have hXdeg1 : (X ^ 2 ^ t * Q t).natDegree ≤ 2 ^ t + (Q t).natDegree := by
        calc
          (X ^ 2 ^ t * Q t).natDegree ≤ (X ^ 2 ^ t).natDegree + (Q t).natDegree :=
            Polynomial.natDegree_mul_le
          _ = 2 ^ t + (Q t).natDegree := by rw [Polynomial.natDegree_X_pow (2 ^ t)]
      have hXdeg : (X ^ 2 ^ t * Q t).natDegree ≤ 2 ^ (t + 1) - 1 := by
        calc
          (X ^ 2 ^ t * Q t).natDegree ≤ 2 ^ t + (Q t).natDegree := hXdeg1
          _ ≤ 2 ^ t + (2 ^ t - 1) := by omega
          _ = 2 ^ (t + 1) - 1 := by rw [pow_two_succ]; omega
      have hbig : 2 ^ (t + 1) - 1 = 2 * 2 ^ t - 1 := by rw [pow_two_succ]
      have hA : (P t).natDegree ≤ 2 ^ (t + 1) - 1 := by
        rw [pow_two_succ]
        omega
      have hXcoeff (j : ℕ) : (X ^ 2 ^ t * Q t).coeff (2 ^ t + j) = (Q t).coeff j := by
        rw [Nat.add_comm]
        exact Polynomial.coeff_X_pow_mul (p := Q t) (n := 2 ^ t) (d := j)
      have hPtop_zero (j : ℕ) : (P t).coeff (2 ^ t + j) = 0 := by
        refine coeff_eq_zero_of_natDegree_lt ?_
        have h1 : 2 ^ t - 1 < 2 ^ t := by omega
        exact lt_of_le_of_lt hdegP (lt_of_lt_of_le h1 (Nat.le_add_right (2 ^ t) j))
      constructor
      · rw [P_succ]
        exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hA hXdeg)
      constructor
      · rw [Q_succ]
        exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le hA hXdeg)
      constructor
      · intro i hi
        by_cases hit : i < 2 ^ t
        · rw [coeff_P_extend t i hit]
          exact hcP i hit
        · have hi2 : i < 2 * 2 ^ t := by simpa [pow_two_succ] using hi
          let j := i - 2 ^ t
          have hj : i = 2 ^ t + j := by
            dsimp [j]
            omega
          have hj2 : j < 2 ^ t := by
            dsimp [j]
            omega
          rw [hj, P_succ, Polynomial.coeff_add, hXcoeff, hPtop_zero, zero_add]
          exact hcQ j hj2
      · intro i hi
        by_cases hit : i < 2 ^ t
        · rw [coeff_Q_extend t i hit]
          exact hcP i hit
        · have hi2 : i < 2 * 2 ^ t := by simpa [pow_two_succ] using hi
          let j := i - 2 ^ t
          have hj : i = 2 ^ t + j := by
            dsimp [j]
            omega
          have hj2 : j < 2 ^ t := by
            dsimp [j]
            omega
          rw [hj, Q_succ, Polynomial.coeff_sub, hXcoeff, hPtop_zero, zero_sub]
          rcases hcQ j hj2 with h | h
          · right; rw [h]
          · left; rw [h]; norm_num

lemma P_natDegree_le (t : ℕ) : (P t).natDegree ≤ 2 ^ t - 1 := (P_Q_bounds t).1
lemma Q_natDegree_le (t : ℕ) : (Q t).natDegree ≤ 2 ^ t - 1 := (P_Q_bounds t).2.1
lemma P_coeff_mem (t i : ℕ) (hi : i < 2 ^ t) : (P t).coeff i = 1 ∨ (P t).coeff i = -1 :=
  (P_Q_bounds t).2.2.1 i hi
lemma Q_coeff_mem (t i : ℕ) (hi : i < 2 ^ t) : (Q t).coeff i = 1 ∨ (Q t).coeff i = -1 :=
  (P_Q_bounds t).2.2.2 i hi

/-- Coefficients of `P t` at indices `≥ 2^t` vanish. -/
lemma coeff_P_ge (t i : ℕ) (hi : 2 ^ t ≤ i) : (P t).coeff i = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
    have h1 : 2 ^ t - 1 < 2 ^ t := by
      have : 0 < 2 ^ t := two_pow_pos t
      omega
    exact lt_of_le_of_lt (P_natDegree_le t) (lt_of_lt_of_le h1 hi))

/-- Coefficients of `Q t` at indices `≥ 2^t` vanish. -/
lemma coeff_Q_ge (t i : ℕ) (hi : 2 ^ t ≤ i) : (Q t).coeff i = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
    have h1 : 2 ^ t - 1 < 2 ^ t := by
      have : 0 < 2 ^ t := two_pow_pos t
      omega
    exact lt_of_le_of_lt (Q_natDegree_le t) (lt_of_lt_of_le h1 hi))

lemma coeff_P_top (t j : ℕ) : (P (t + 1)).coeff (2 ^ t + j) = (Q t).coeff j := by
  rw [P_succ, Polynomial.coeff_add]
  have hX : (X ^ 2 ^ t * Q t).coeff (2 ^ t + j) = (Q t).coeff j := by
    convert Polynomial.coeff_X_pow_mul (p := Q t) (n := 2 ^ t) (d := j) using 1
    rw [Nat.add_comm]
  have hP : (P t).coeff (2 ^ t + j) = 0 := coeff_P_ge t (2 ^ t + j) (by omega)
  rw [hX, hP, zero_add]

lemma coeff_Q_top (t j : ℕ) : (Q (t + 1)).coeff (2 ^ t + j) = - (Q t).coeff j := by
  rw [Q_succ, Polynomial.coeff_sub]
  have hX : (X ^ 2 ^ t * Q t).coeff (2 ^ t + j) = (Q t).coeff j := by
    convert Polynomial.coeff_X_pow_mul (p := Q t) (n := 2 ^ t) (d := j) using 1
    rw [Nat.add_comm]
  have hP : (P t).coeff (2 ^ t + j) = 0 := coeff_P_ge t (2 ^ t + j) (by omega)
  rw [hX, hP, zero_sub]



lemma normSq_add_sub (a b : ℂ) : normSq (a + b) + normSq (a - b) = 2 * (normSq a + normSq b) := by
  simp only [normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

lemma normSq_mul_pow (z : ℂ) (m : ℕ) : normSq (z ^ m) = normSq z ^ m := by
  exact map_pow normSq z m

/-- Fundamental Rudin-Shapiro identity: `|P_t(z)|² + |Q_t(z)|² = 2^{t+1}` on `|z| = 1`. -/
lemma normSq_eval_add (t : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    normSq ((P t).eval z) + normSq ((Q t).eval z) = 2 ^ (t + 1) := by
  induction t with
  | zero =>
      have hz2 : normSq z = 1 := by rw [← Complex.sq_norm z, hz]; norm_num
      simp [hz2]
      norm_num
  | succ t ih =>
      rw [eval_P_succ, eval_Q_succ]
      have hu : normSq (z ^ 2 ^ t) = 1 := by
        rw [normSq_mul_pow]
        have hz2 : normSq z = 1 := by rw [← Complex.sq_norm z, hz]; norm_num
        simp [hz2]
      have h := normSq_add_sub ((P t).eval z) (z ^ 2 ^ t * (Q t).eval z)
      rw [normSq_mul, hu, one_mul] at h
      rw [h]
      rw [ih]
      rw [mul_comm, ← pow_succ]

/-- `|P_t(z)| ≤ sqrt(2^{t+1})` on `|z|=1`. -/
lemma norm_P_eval_le (t : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(P t).eval z‖ ≤ Real.sqrt (2 ^ (t + 1)) := by
  have hsq : ‖(P t).eval z‖ ^ 2 ≤ (2 : ℝ) ^ (t + 1) := by
    rw [Complex.sq_norm]
    have h := normSq_eval_add t z hz
    have hn : 0 ≤ normSq ((Q t).eval z) := normSq_nonneg _
    nlinarith
  have hnonneg : 0 ≤ ‖(P t).eval z‖ := norm_nonneg _
  exact (Real.le_sqrt hnonneg (by positivity : 0 ≤ (2 : ℝ) ^ (t + 1))).mpr hsq

/-- `|Q_t(z)| ≤ sqrt(2^{t+1})` on `|z|=1`. -/
lemma norm_Q_eval_le (t : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(Q t).eval z‖ ≤ Real.sqrt (2 ^ (t + 1)) := by
  have hsq : ‖(Q t).eval z‖ ^ 2 ≤ (2 : ℝ) ^ (t + 1) := by
    rw [Complex.sq_norm]
    have h := normSq_eval_add t z hz
    have hn : 0 ≤ normSq ((P t).eval z) := normSq_nonneg _
    nlinarith
  have hnonneg : 0 ≤ ‖(Q t).eval z‖ := norm_nonneg _
  exact (Real.le_sqrt hnonneg (by positivity : 0 ≤ (2 : ℝ) ^ (t + 1))).mpr hsq

end RudinShapiro
end Submission
