import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.PowerSeries.Basic

/-! Work file: prove `mul_comp_neg_coeff_odd`. -/
noncomputable section
open Polynomial
open scoped Polynomial

namespace Submission.PowersOdd

/-- `(-X)^k = C((-1)^k) * X^k`. -/
lemma neg_X_pow_eq {R : Type*} [CommRing R] (k : ℕ) :
    (-X : R[X]) ^ k = C ((-1 : R) ^ k) * X ^ k := by
  calc
    (-X : R[X]) ^ k = (-1 : R[X]) ^ k * X ^ k := by rw [neg_pow]
    _ = C ((-1 : R) ^ k) * X ^ k := by
      congr 1
      calc
        (-1 : R[X]) ^ k = (C (-1 : R)) ^ k := by
          rw [show (-1 : R[X]) = C (-1 : R) by simp]
        _ = C ((-1 : R) ^ k) := by rw [Polynomial.C_pow]

/-- The `n`-th coefficient of `(-X)^k`. -/
lemma coeff_neg_X_pow {R : Type*} [CommRing R] (k n : ℕ) :
    ((-X : R[X]) ^ k).coeff n = if n = k then (-1 : R) ^ k else 0 := by
  rw [neg_X_pow_eq]
  rw [Polynomial.coeff_C_mul_X_pow]

/-- Coefficients of the monomial case of composing with `-X`: substituting
`-X` sends the basis monomial `X^k` to `(-1)^k X^k`. -/
lemma coeff_comp_neg_X {R : Type*} [CommRing R] (Q : R[X]) (n : ℕ) :
    (Q.comp (-X)).coeff n = (-1 : R) ^ n * Q.coeff n := by
  classical
  induction Q using Polynomial.induction_on' with
  | add Q1 Q2 h1 h2 =>
      rw [add_comp, coeff_add, coeff_add, h1, h2]
      ring
  | monomial k a =>
      rw [Polynomial.monomial_comp]
      rw [Polynomial.coeff_C_mul]
      rw [coeff_neg_X_pow]
      rw [Polynomial.coeff_monomial]
      by_cases h : k = n
      · subst n
        simp
        ring
      · have h' : ¬ n = k := by exact fun hn => h hn.symm
        simp [h, h']

/-- `P(X)P(-X)` has vanishing odd-degree coefficients, in a domain of
characteristic not two.  Sketch: let `F := P * P.comp (-X)`.  Then
`F.comp (-X) = F`, and one checks `(F.comp (-X)).coeff n = (-1)^n F.coeff n`,
so for odd `n`, `F.coeff n = - F.coeff n`, and since `2 ≠ 0` in a domain,
`F.coeff n = 0`. -/
lemma mul_comp_neg_coeff_odd {R : Type*} [CommRing R] [IsDomain R]
    (hchar : (2 : R) ≠ 0) (P : R[X]) :
    ∀ n : ℕ, ¬ Even n → (P * P.comp (-X)).coeff n = 0 := by
  classical
  intro n hn
  let F : R[X] := P * P.comp (-X)
  have hF : F.comp (-X) = F := by
    dsimp [F]
    calc
      (P * P.comp (-X)).comp (-X) = P.comp (-X) * (P.comp (-X)).comp (-X) := by
        rw [mul_comp_neg_X]
      _ = P.comp (-X) * P := by rw [comp_neg_X_comp_neg_X]
      _ = P * P.comp (-X) := by rw [mul_comm]
  have hc : (F.comp (-X)).coeff n = (-1 : R) ^ n * F.coeff n :=
    coeff_comp_neg_X F n
  have hnegpow : (-1 : R) ^ n = -1 := by
    rw [neg_one_pow_eq_ite]
    simp [hn]
  have hmain : F.coeff n = -F.coeff n := by
    calc
      F.coeff n = (F.comp (-X)).coeff n := by rw [hF]
      _ = (-1 : R) ^ n * F.coeff n := hc
      _ = -1 * F.coeff n := by rw [hnegpow]
      _ = -F.coeff n := by simp
  have hcc : F.coeff n + F.coeff n = 0 := by
    nth_rewrite 1 [hmain]
    simp
  have htwomul : (2 : R) * F.coeff n = 0 := by
    calc
      (2 : R) * F.coeff n = F.coeff n + F.coeff n := by rw [two_mul]
      _ = 0 := hcc
  have hc0 : F.coeff n = 0 := by
    rcases mul_eq_zero.mp htwomul with h2 | hc0
    · exact False.elim (hchar h2)
    · exact hc0
  simpa [F] using hc0

end Submission.PowersOdd
end
