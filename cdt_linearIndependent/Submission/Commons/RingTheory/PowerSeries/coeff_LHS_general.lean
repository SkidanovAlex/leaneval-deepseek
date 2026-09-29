import Mathlib
import Submission.Commons.RingTheory.PowerSeries.logPA_ode

open PowerSeries

namespace Commons.RingTheory.PowerSeries

noncomputable section

/-! ## Generic coefficient plumbing

The lemmas `monDer2`, `monDer`, `monY`, `coeff_P2_der2_full`, `coeff_P1_der_full`,
`coeff_P0_full`, `coeff_LHS_eq_c7sum` of `logPA_ode` are stated for the specific
series `Yser a b = mk (fun m => ycoef a b m)`.  Every step of those proofs only
uses `coeff m (Yser a b) = ycoef a b m` and the general monomial coefficient
lemmas, so here we restate all of them for an *arbitrary* power series `Y`.  The
general certificate `coeff_LHS_general` then follows by taking
`Y = mk (fun m => f m * g m)` and invoking `claim7`.
-/

/-- generic `coeff_P2_der2_full`: coefficient of `P2·Y''` at `x^n`, `n ≥ 7`. -/
lemma coeff_P2_der2_full_gen (a b : ℚ) (Y : PowerSeries ℚ) (n : ℕ) (hn : 7 ≤ n) :
    coeff n (P2sum a b * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Y))) =
      (-1 : ℚ) * ((((n - 1 + 1) * (n - 1 + 2) : ℕ) : ℚ)) * coeff ((n - 1) + 2) Y
      + (4 * a * b) * ((((n - 2 + 1) * (n - 2 + 2) : ℕ) : ℚ)) * coeff ((n - 2) + 2) Y
      + (3 - 4 * a ^ 2 - 4 * b ^ 2) * ((((n - 3 + 1) * (n - 3 + 2) : ℕ) : ℚ)) * coeff ((n - 3) + 2) Y
      + (4 * a ^ 2 + 4 * b ^ 2 - 3) * ((((n - 5 + 1) * (n - 5 + 2) : ℕ) : ℚ)) * coeff ((n - 5) + 2) Y
      - (4 * a * b) * ((((n - 6 + 1) * (n - 6 + 2) : ℕ) : ℚ)) * coeff ((n - 6) + 2) Y
      + (1 : ℚ) * ((((n - 7 + 1) * (n - 7 + 2) : ℕ) : ℚ)) * coeff ((n - 7) + 2) Y := by
  let D2 : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Y)
  have mX1 : coeff n ((-X) * D2) = - ((((n - 1 + 1) * (n - 1 + 2) : ℕ) : ℚ) * coeff ((n - 1) + 2) Y) := by
    have hX0 : coeff n (X * D2) = coeff (n - 1) D2 := by
      simpa using (coeff_X_pow_mul D2 n 1 (by omega))
    have hX : coeff n (X * D2) = ((((n - 1 + 1) * (n - 1 + 2) : ℕ) : ℚ)) * coeff ((n - 1) + 2) Y := by
      rw [hX0, coeff_der2]
    have hneg : coeff n ((-X) * D2) = - coeff n (X * D2) := by simp
    rw [hneg, hX]
  have mC2 : coeff n (C (4 * a * b) * X ^ 2 * D2) = (4 * a * b) * ((((n - 2 + 1) * (n - 2 + 2) : ℕ) : ℚ)) * coeff ((n - 2) + 2) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul D2 n 2 (by omega)]
    rw [coeff_der2]
    ring
  have mC3 : coeff n (C (3 - 4 * a ^ 2 - 4 * b ^ 2) * X ^ 3 * D2) = (3 - 4 * a ^ 2 - 4 * b ^ 2) * ((((n - 3 + 1) * (n - 3 + 2) : ℕ) : ℚ)) * coeff ((n - 3) + 2) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul D2 n 3 (by omega)]
    rw [coeff_der2]
    ring
  have mC5 : coeff n (C (4 * a ^ 2 + 4 * b ^ 2 - 3) * X ^ 5 * D2) = (4 * a ^ 2 + 4 * b ^ 2 - 3) * ((((n - 5 + 1) * (n - 5 + 2) : ℕ) : ℚ)) * coeff ((n - 5) + 2) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul D2 n 5 (by omega)]
    rw [coeff_der2]
    ring
  have mC6 : coeff n (C (4 * a * b) * X ^ 6 * D2) = (4 * a * b) * ((((n - 6 + 1) * (n - 6 + 2) : ℕ) : ℚ)) * coeff ((n - 6) + 2) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul D2 n 6 (by omega)]
    rw [coeff_der2]
    ring
  have mO7 : coeff n (X ^ 7 * D2) = ((((n - 7 + 1) * (n - 7 + 2) : ℕ) : ℚ)) * coeff ((n - 7) + 2) Y := by
    rw [coeff_X_pow_mul D2 n 7 (by omega)]
    rw [coeff_der2]
  unfold P2sum
  change coeff n ((-X + C (4 * a * b) * X ^ 2 + C (3 - 4 * a ^ 2 - 4 * b ^ 2) * X ^ 3
      + C (4 * a ^ 2 + 4 * b ^ 2 - 3) * X ^ 5 - C (4 * a * b) * X ^ 6 + X ^ 7) * D2) = _
  simp only [add_mul, sub_mul]
  simp only [coeff_add_s, coeff_sub_s]
  rw [mX1, mC2, mC3, mC5, mC6, mO7]
  ring_nf <;> norm_num

/-- generic `coeff_P1_der_full`: coefficient of `P1·Y'` at `x^n`, `n ≥ 7`. -/
lemma coeff_P1_der_full_gen (a b : ℚ) (Y : PowerSeries ℚ) (n : ℕ) (hn : 7 ≤ n) :
    coeff n (P1fac a b * PowerSeries.derivative (R := ℚ) Y) =
      - (((n + 1 : ℕ) : ℚ)) * coeff (n + 1) Y
      + (8 * a * b) * ((((n - 1 + 1) : ℕ) : ℚ)) * coeff ((n - 1) + 1) Y
      + (5 - 12 * a ^ 2 - 12 * b ^ 2) * ((((n - 2 + 1) : ℕ) : ℚ)) * coeff ((n - 2) + 1) Y
      + (16 * a * b) * ((((n - 3 + 1) : ℕ) : ℚ)) * coeff ((n - 3) + 1) Y
      + (4 * a ^ 2 + 4 * b ^ 2 - 7) * ((((n - 4 + 1) : ℕ) : ℚ)) * coeff ((n - 4) + 1) Y
      - (8 * a * b) * ((((n - 5 + 1) : ℕ) : ℚ)) * coeff ((n - 5) + 1) Y
      + 3 * ((((n - 6 + 1) : ℕ) : ℚ)) * coeff ((n - 6) + 1) Y := by
  let E1 : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) Y
  have hm0 : coeff n (((-1 : PowerSeries ℚ)) * E1) = - (((n + 1 : ℕ) : ℚ)) * coeff (n + 1) Y := by
    have hE : coeff n E1 = ((n + 1 : ℕ)) * coeff (n + 1) Y := by
      rw [PowerSeries.coeff_derivative]
      simp <;> ring
    have hneg : coeff n (((-1 : PowerSeries ℚ)) * E1) = - coeff n E1 := by
      rw [show ((-1 : PowerSeries ℚ)) * E1 = - E1 by simp]
      simp
    rw [hneg, hE] <;> ring
  have hm1 : coeff n (C (8 * a * b) * X * E1) = (8 * a * b) * ((((n - 1 + 1) : ℕ) : ℚ)) * coeff ((n - 1) + 1) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    have hX : coeff n (X * E1) = coeff (n - 1) E1 := by
      simpa using (coeff_X_pow_mul E1 n 1 (by omega))
    rw [hX]
    rw [PowerSeries.coeff_derivative]
    simp <;> ring
  have hm2 : coeff n (C (5 - 12 * a ^ 2 - 12 * b ^ 2) * X ^ 2 * E1) = (5 - 12 * a ^ 2 - 12 * b ^ 2) * ((((n - 2 + 1) : ℕ) : ℚ)) * coeff ((n - 2) + 1) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul E1 n 2 (by omega)]
    rw [PowerSeries.coeff_derivative]
    simp <;> ring
  have hm3 : coeff n (C (16 * a * b) * X ^ 3 * E1) = (16 * a * b) * ((((n - 3 + 1) : ℕ) : ℚ)) * coeff ((n - 3) + 1) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul E1 n 3 (by omega)]
    rw [PowerSeries.coeff_derivative]
    simp <;> ring
  have hm4 : coeff n (C (4 * a ^ 2 + 4 * b ^ 2 - 7) * X ^ 4 * E1) = (4 * a ^ 2 + 4 * b ^ 2 - 7) * ((((n - 4 + 1) : ℕ) : ℚ)) * coeff ((n - 4) + 1) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul E1 n 4 (by omega)]
    rw [PowerSeries.coeff_derivative]
    simp <;> ring
  have hm5 : coeff n (C (8 * a * b) * X ^ 5 * E1) = (8 * a * b) * ((((n - 5 + 1) : ℕ) : ℚ)) * coeff ((n - 5) + 1) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul E1 n 5 (by omega)]
    rw [PowerSeries.coeff_derivative]
    simp <;> ring
  have hm6 : coeff n (3 * X ^ 6 * E1) = 3 * ((((n - 6 + 1) : ℕ) : ℚ)) * coeff ((n - 6) + 1) Y := by
    have hc : (3 : PowerSeries ℚ) = C (3 : ℚ) := C_natCast 3
    rw [hc, mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul E1 n 6 (by omega)]
    rw [PowerSeries.coeff_derivative]
    simp <;> ring
  unfold P1fac
  change coeff n (((-1 : PowerSeries ℚ) + C (8 * a * b) * X + C (5 - 12 * a ^ 2 - 12 * b ^ 2) * X ^ 2 + C (16 * a * b) * X ^ 3 + C (4 * a ^ 2 + 4 * b ^ 2 - 7) * X ^ 4 - C (8 * a * b) * X ^ 5 + 3 * X ^ 6) * E1) = _
  simp only [add_mul, sub_mul]
  simp only [coeff_add_s, coeff_sub_s]
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  ring_nf <;> exact C_natCast 3

/-- generic `coeff_P0_full`: coefficient of `P0·Y` at `x^n`, `n ≥ 7`. -/
lemma coeff_P0_full_gen (a b : ℚ) (Y : PowerSeries ℚ) (n : ℕ) (hn : 7 ≤ n) :
    coeff n (P0fac a b * Y) =
      (a * b) * coeff n Y
      + (1 - 3 * a ^ 2 - 3 * b ^ 2) * coeff (n - 1) Y
      + (8 * a * b) * coeff (n - 2) Y
      - (a ^ 2 + b ^ 2 + 2) * coeff (n - 3) Y
      - (a * b) * coeff (n - 4) Y
      + coeff (n - 5) Y := by
  have h0 : coeff n (C ((a * b)) * Y) = (a * b) * coeff n Y := by
    rw [_root_.PowerSeries.coeff_C_mul]
  have h1 : coeff n (C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X * Y) = (1 - 3 * a ^ 2 - 3 * b ^ 2) * coeff (n - 1) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    have hX : coeff n (X * Y) = coeff (n - 1) Y := by
      simpa using (coeff_X_pow_mul Y n 1 (by omega))
    rw [hX]
  have h2 : coeff n (C ((8 * a * b)) * X ^ 2 * Y) = (8 * a * b) * coeff (n - 2) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul Y n 2 (by omega)]
  have h3 : coeff n (C ((a ^ 2 + b ^ 2 + 2)) * X ^ 3 * Y) = (a ^ 2 + b ^ 2 + 2) * coeff (n - 3) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul Y n 3 (by omega)]
  have h4 : coeff n (C ((a * b)) * X ^ 4 * Y) = (a * b) * coeff (n - 4) Y := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul Y n 4 (by omega)]
  have h5 : coeff n (X ^ 5 * Y) = coeff (n - 5) Y := by
    rw [coeff_X_pow_mul Y n 5 (by omega)]
  unfold P0fac
  change coeff n ((C (a * b) + C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X + C (8 * a * b) * X ^ 2 - C (a ^ 2 + b ^ 2 + 2) * X ^ 3 - C (a * b) * X ^ 4 + X ^ 5) * Y) = _
  simp only [add_mul, sub_mul]
  simp only [coeff_add_s, coeff_sub_s]
  rw [h0, h1, h2, h3, h4, h5] <;> ring

/-- generic `c7sum`: the seven-term combination of coefficients of an arbitrary `Y`. -/
def c7sum_gen (a b : ℚ) (Y : PowerSeries ℚ) (n : ℕ) : ℚ :=
  dd0 ((n - 5 : ℕ) : ℚ) a b * coeff (n - 5) Y
    + dd1 ((n - 5 : ℕ) : ℚ) a b * coeff (n - 4) Y
    + dd2 ((n - 5 : ℕ) : ℚ) a b * coeff (n - 3) Y
    + dd3 ((n - 5 : ℕ) : ℚ) a b * coeff (n - 2) Y
    + dd4 ((n - 5 : ℕ) : ℚ) a b * coeff (n - 1) Y
    + dd5 ((n - 5 : ℕ) : ℚ) a b * coeff n Y
    + dd6 ((n - 5 : ℕ) : ℚ) a b * coeff (n + 1) Y

/-- generic `coeff_LHS_eq_c7sum`: the coefficient of the CDT operator applied to
an arbitrary `Y` is the seven-term combination `c7sum_gen`. -/
lemma coeff_op_eq_c7sum_gen (a b : ℚ) (Y : PowerSeries ℚ) (n : ℕ) (hn : 7 ≤ n) :
    coeff n (P2fac a b * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Y)
        + P1fac a b * PowerSeries.derivative (R := ℚ) Y + P0fac a b * Y) = c7sum_gen a b Y n := by
  rw [P2fac_eq_sum]
  simp only [coeff_add_s]
  rw [coeff_P2_der2_full_gen a b Y n hn, coeff_P1_der_full_gen a b Y n hn,
    coeff_P0_full_gen a b Y n hn]
  rw [show (n - 7) + 1 = n - 6 by omega]
  rw [show (n - 1) + 1 = n by omega]
  rw [show (n - 1) + 2 = n + 1 by omega]
  rw [show (n - 2) + 1 = n - 1 by omega]
  rw [show (n - 2) + 2 = n by omega]
  rw [show (n - 3) + 1 = n - 2 by omega]
  rw [show (n - 3) + 2 = n - 1 by omega]
  rw [show (n - 4) + 1 = n - 3 by omega]
  rw [show (n - 5) + 1 = n - 4 by omega]
  rw [show (n - 5) + 2 = n - 3 by omega]
  rw [show (n - 6) + 1 = n - 5 by omega]
  rw [show (n - 6) + 2 = n - 4 by omega]
  rw [show (n - 7) + 2 = n - 5 by omega]
  push_cast
  unfold c7sum_gen
  rw [show ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 by rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
  rw [show ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 by rw [Nat.cast_sub (by omega : 2 ≤ n)]; norm_num]
  rw [show ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 by rw [Nat.cast_sub (by omega : 3 ≤ n)]; norm_num]
  rw [show ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 by rw [Nat.cast_sub (by omega : 4 ≤ n)]; norm_num]
  rw [show ((n - 5 : ℕ) : ℚ) = (n : ℚ) - 5 by rw [Nat.cast_sub (by omega : 5 ≤ n)]; norm_num]
  rw [show ((n - 6 : ℕ) : ℚ) = (n : ℚ) - 6 by rw [Nat.cast_sub (by omega : 6 ≤ n)]; norm_num]
  ring

/-- **General certificate for the CDT order-2 Hadamard-product operator**
(arXiv:2408.15403 eq. (ODE)).  For *any* pair of coefficient sequences `f`,
`g` satisfying the three-term Legendre recurrences `RecProp a f`, `RecProp b g`,
the `x^n`-coefficient (`n ≥ 7`) of the operator `P2·Y'' + P1·Y' + P0·Y`
applied to the Hadamard product `Y = mk (fun m => f m * g m)` vanishes.

This generalises `coeff_LHS_zero` of the imported module (its special case
`f = usum a`, `g = usum b`): the linear-algebra certificate `claim7` there is
already stated for arbitrary `RecProp` sequences, so only the coefficient
plumbing is restated for the general product sequence `fun m => f m * g m`
above, and then `claim7 a b hf hg` is fed into that plumbing exactly as
`c7sum_zero` does for `usum`. -/
theorem coeff_LHS_general (a b : ℚ) {f g : ℕ → ℚ}
    (hf : Commons.RingTheory.PowerSeries.RecProp a f)
    (hg : Commons.RingTheory.PowerSeries.RecProp b g)
    (n : ℕ) (hn : 7 ≤ n) :
    PowerSeries.coeff n
      (Commons.RingTheory.PowerSeries.P2fac a b
          * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (PowerSeries.mk (fun m => f m * g m)))
        + Commons.RingTheory.PowerSeries.P1fac a b
          * PowerSeries.derivative (R := ℚ) (PowerSeries.mk (fun m => f m * g m))
        + Commons.RingTheory.PowerSeries.P0fac a b
          * PowerSeries.mk (fun m => f m * g m)) = 0 := by
  have h := coeff_op_eq_c7sum_gen a b (PowerSeries.mk (fun m => f m * g m)) n hn
  rw [h]
  unfold c7sum_gen
  simp only [PowerSeries.coeff_mk]
  have hc := claim7 a b hf hg (n - 5)
  rw [show (n - 5) + 0 = n - 5 by omega,
      show (n - 5) + 1 = n - 4 by omega,
      show (n - 5) + 2 = n - 3 by omega,
      show (n - 5) + 3 = n - 2 by omega,
      show (n - 5) + 4 = n - 1 by omega,
      show (n - 5) + 5 = n by omega,
      show (n - 5) + 6 = n + 1 by omega] at hc
  linear_combination hc

end

end Commons.RingTheory.PowerSeries
