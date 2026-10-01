import Mathlib
import Submission.Work.LinnikBurgess.cubic_phase_defs

/-!
# Auxiliary algebra for the cubic root-sum decomposition

This module collects the algebraic identities underlying
`Work.LinnikBurgess.cubicPhase_rootSum`:

* `resPoly_eval` / `resPoly_mul_eval`: the remainder polynomial `resPoly` is the
  `p²`-normalised Taylor remainder of `R` at a point `c`;
* `eval_add_expansion`: the second order Taylor expansion with Hasse derivatives;
* `shiftPhase_CubicPhase_eval`: `H(c + p·u) = H(c) + p² · shiftPhase(c)(u)`, the
  stationary-phase identity at a critical point `c` of `linCoeff`;
* `deriv_CubicPhase_eval` / `dvd_deriv_iff_dvd_linCoeff`: the derivative criterion
  `p ∣ H'(c) ↔ p ∣ linCoeff(c)`.
-/

namespace Work.LinnikBurgess

open Polynomial

/-- Evaluation of the remainder polynomial as a Hasse-derivative expansion. -/
lemma resPoly_eval (p : ℕ) (R : Polynomial ℤ) (c : ℕ) (u : ℤ) :
    Polynomial.eval u (resPoly p R c)
      = ∑ n ∈ Finset.range (R.natDegree - 1),
          Polynomial.eval (c:ℤ) (Polynomial.hasseDeriv (n + 2) R) * (p:ℤ) ^ n * u ^ (n + 2) := by
  simp only [resPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Second order Taylor expansion of a polynomial with integer coefficients. -/
lemma eval_add_expansion (R : Polynomial ℤ) (c y : ℤ) :
    Polynomial.eval (c + y) R
      = Polynomial.eval c R + y * Polynomial.eval c (Polynomial.derivative R)
        + y ^ 2 * ∑ n ∈ Finset.range (R.natDegree - 1),
            Polynomial.eval c (Polynomial.hasseDeriv (n + 2) R) * y ^ n := by
  rw [Commons.Algebra.Polynomial.eval_add_eq_sum_hasseDeriv R c y]
  rcases Nat.eq_zero_or_pos R.natDegree with hd | hd
  · rw [hd, Finset.sum_range_one]
    have hz : Polynomial.hasseDeriv 1 R = 0 :=
      Polynomial.hasseDeriv_eq_zero_of_lt_natDegree (n := 1) R (by rw [hd]; norm_num)
    have hz2 : Polynomial.eval c (Polynomial.derivative R) = 0 := by
      rw [← Polynomial.hasseDeriv_one', hz, Polynomial.eval_zero]
    rw [Polynomial.hasseDeriv_zero', hz2]
    simp
  · have hd2 : 2 + (R.natDegree - 1) = R.natDegree + 1 := by omega
    rw [← hd2,
      Finset.sum_range_add (fun n => Polynomial.eval c ((Polynomial.hasseDeriv n) R) * y ^ n) 2
        (R.natDegree - 1),
      show ∑ x ∈ Finset.range 2, Polynomial.eval c ((Polynomial.hasseDeriv x) R) * y ^ x
          = Polynomial.eval c R + y * Polynomial.eval c (Polynomial.derivative R) from by
        rw [show (2:ℕ) = 1 + 1 by norm_num, Finset.sum_range_succ, Finset.sum_range_one,
          Polynomial.hasseDeriv_zero', Polynomial.hasseDeriv_one']
        ring,
      Finset.mul_sum, add_right_inj]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.add_comm 2 n, pow_add]
    ring

/-- `p² · resPoly` is the second order Taylor remainder of `R`. -/
lemma resPoly_mul_eval (p : ℕ) (R : Polynomial ℤ) (c : ℕ) (u : ℤ) :
    (p:ℤ)^2 * Polynomial.eval u (resPoly p R c)
      = Polynomial.eval ((c:ℤ) + (p:ℤ)*u) R - Polynomial.eval (c:ℤ) R
        - (p:ℤ)*u * Polynomial.eval (c:ℤ) (Polynomial.derivative R) := by
  rw [eval_add_expansion R (c:ℤ) ((p:ℤ)*u), resPoly_eval]
  have hsum : (p:ℤ)^2 * (∑ n ∈ Finset.range (R.natDegree - 1),
        Polynomial.eval (c:ℤ) (Polynomial.hasseDeriv (n+2) R) * (p:ℤ)^n * u^(n+2))
      = ((p:ℤ)*u)^2 * ∑ n ∈ Finset.range (R.natDegree - 1),
        Polynomial.eval (c:ℤ) (Polynomial.hasseDeriv (n+2) R) * ((p:ℤ)*u)^n := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [mul_pow]
    ring
  rw [hsum]
  ring

/-- The stationary-phase identity: at a critical point `c` of `linCoeff`, shifting the
variable by `p·u` changes the cubic phase by `p² · shiftPhase(c)(u)`. -/
lemma shiftPhase_CubicPhase_eval (p : ℕ) (β γ δ : ℤ) (R : Polynomial ℤ) (c : ℕ)
    (hdiv : (p:ℤ) ∣ linCoeff β γ δ c) (u : ℤ) :
    Polynomial.eval ((c:ℤ) + (p:ℤ)*u) (CubicPhase p β γ δ R)
      = Polynomial.eval (c:ℤ) (CubicPhase p β γ δ R)
        + (p:ℤ)^2 * Polynomial.eval u (shiftPhase p β γ δ R c) := by
  have hp : (p:ℤ) * (linCoeff β γ δ c / (p:ℤ)) = linCoeff β γ δ c := by
    rw [mul_comm, Int.ediv_mul_cancel hdiv]
  have hpp' : (p:ℤ)^2 * u * (linCoeff β γ δ c / (p:ℤ)) = (p:ℤ) * u * linCoeff β γ δ c := by
    rw [show (p:ℤ)^2 * u * (linCoeff β γ δ c / (p:ℤ))
        = u * ((p:ℤ)^2 * (linCoeff β γ δ c / (p:ℤ))) by ring,
      show (p:ℤ)^2 * (linCoeff β γ δ c / (p:ℤ)) = (p:ℤ) * linCoeff β γ δ c by
        rw [pow_two, mul_assoc, hp]]
    ring
  have h3 : (p:ℤ)^3 * Polynomial.eval u (resPoly p R c)
      = (p:ℤ) * (Polynomial.eval ((c:ℤ) + (p:ℤ)*u) R - Polynomial.eval (c:ℤ) R
          - (p:ℤ)*u * Polynomial.eval (c:ℤ) (Polynomial.derivative R)) := by
    rw [← resPoly_mul_eval p R c u]; ring
  simp only [CubicPhase, shiftPhase, quadCoeff, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  ring_nf
  rw [h3]
  ring_nf
  rw [hpp']
  simp only [linCoeff]
  ring

/-- The derivative of the cubic phase at an integer point. -/
lemma deriv_CubicPhase_eval (p : ℕ) (β γ δ : ℤ) (R : Polynomial ℤ) (c : ℕ) :
    Polynomial.eval (c : ℤ) (Polynomial.derivative (CubicPhase p β γ δ R))
      = linCoeff β γ δ c + (p : ℤ) * Polynomial.eval (c : ℤ) (Polynomial.derivative R) := by
  simp only [CubicPhase, linCoeff, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_pow,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_zero]
  ring

/-- The critical-point criterion: `p` divides `H'(c)` exactly when `p` divides `linCoeff(c)`. -/
lemma dvd_deriv_iff_dvd_linCoeff (p : ℕ) (β γ δ : ℤ) (R : Polynomial ℤ) (a : ℕ) :
    ((p:ℤ) ∣ Polynomial.eval (a:ℤ) (Polynomial.derivative (CubicPhase p β γ δ R)))
      ↔ (p:ℤ) ∣ linCoeff β γ δ a := by
  rw [deriv_CubicPhase_eval]
  exact dvd_add_left (dvd_mul_right (p:ℤ) _)

/-- Rewriting a range sum with an `if` into a `filter`ed sum. -/
lemma sum_range_ite_mul_filter (p : ℕ) (P : ℕ → Prop) [DecidablePred P] (S : ℕ → ℂ) :
    (∑ a ∈ Finset.range p, (if P a then (p:ℂ) else 0) * S a)
      = (p:ℂ) * ∑ a ∈ (Finset.range p).filter P, S a := by
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : P a
  · simp [h]
  · simp [h]

end Work.LinnikBurgess
