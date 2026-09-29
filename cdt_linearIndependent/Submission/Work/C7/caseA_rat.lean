import Mathlib
import Submission.Work.C7.caseA_setup
import Submission.Work.C7.rat_ode2

/-!
# Area C7 — the "rational" end of case A (`Work.C7.caseA_rat`)

`Work.C7.caseA_setup` reduces case A of the `seven`-independence argument to a *polynomial*
relation
`x(x-1)²·(d·(C 3)' - d'·(C 3)) + 2d²(x-2)² = 0`, and observes that, clearing the irrelevant
factor `x` and dividing by `d²`, it says that the rational function `(C 3 / d)` has derivative
`-2(x-2)²/(x-1)²`.  By `Work.C7.rat_ode2` no rational function has that derivative (the equation
`dRat δ = 2(x-2)²(x-1)⁻²` has no solution: at `X = 1` the right-hand side has a *double* pole,
while a derivative never has a simple pole).

This file supplies the missing elementary step: from the polynomial identity
`(X-1)²·(c'd - cd') + 2d²(X-2)² = 0` (with `d ≠ 0`) one *constructs* the offending rational
function `δ = -(c/d) ∈ ℚ(X)` and computes `dRat δ = 2(X-2)²((X-1)²)⁻¹`.
-/

noncomputable section

namespace Work.C7

open Polynomial

/-- **No rational function solves the first ODE of `Work.C7.rat_ode2`**, in polynomial form.

If `c, d ∈ ℚ[X]` with `d ≠ 0` satisfy the identity
`(X-1)²·(c'd - cd') + 2d²(X-2)² = 0`, then the rational function `-(c/d)` would have derivative
`2(X-2)²/(X-1)²`, which is impossible (`Work.C7.rat_ode2`). -/
theorem caseA_rat (d c : Polynomial ℚ) (hd : d ≠ 0)
    (hN1 : ∀ δ : RatFunc ℚ, Submission.CDT.dRat δ
      ≠ 2 * (RatFunc.X - 2) ^ 2 * ((RatFunc.X - 1) ^ 2)⁻¹)
    (h : (Polynomial.X - 1) ^ 2 * (c.derivative * d - c * d.derivative)
        + 2 * d ^ 2 * (Polynomial.X - 2) ^ 2 = 0) : False := by
  -- The candidate rational function is `-(c/d)`; we compute its `dRat`.
  let Φ : Polynomial ℚ →+* RatFunc ℚ := algebraMap (Polynomial ℚ) (RatFunc ℚ)
  have hX1 : Φ (Polynomial.X - 1) = (RatFunc.X : RatFunc ℚ) - 1 := by
    show (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (Polynomial.X - 1) = _
    rw [map_sub, RatFunc.algebraMap_X, map_one]
  have hX2 : Φ (Polynomial.X - 2) = (RatFunc.X : RatFunc ℚ) - 2 := by
    show (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (Polynomial.X - 2) = _
    rw [map_sub, RatFunc.algebraMap_X, map_ofNat]
  -- The polynomial identity, transported to `ℚ(X)`.
  have hR : ((RatFunc.X : RatFunc ℚ) - 1) ^ 2 * Φ (c.derivative * d - c * d.derivative)
      + 2 * (Φ d) ^ 2 * ((RatFunc.X : RatFunc ℚ) - 2) ^ 2 = 0 := by
    have hh := congrArg Φ h
    simp only [map_add, map_mul, map_pow, map_ofNat, map_zero, hX1, hX2] at hh
    exact hh
  have hD : Φ d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hX1ne : ((RatFunc.X : RatFunc ℚ) - 1) ≠ 0 := by
    rw [← hX1]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero 1)
  have hA : ((RatFunc.X : RatFunc ℚ) - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hX1ne
  -- The contradiction: `-(c/d)` is exactly the culprit forbidden by `hN1`.
  refine hN1 (-(Φ c / Φ d)) ?_
  have hcd : Submission.CDT.dRat (Φ c / Φ d)
      = Φ (c.derivative * d - c * d.derivative) / (Φ d) ^ 2 := by
    show Submission.CDT.dRat ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) c /
            (algebraMap (Polynomial ℚ) (RatFunc ℚ)) d) = _
    rw [Submission.CDT.dRat_div]
  rw [Submission.CDT.dRat_neg, hcd]
  -- Solve the transported identity for the numerator `Φ(c'd - cd')`.
  have hvanish : ((RatFunc.X : RatFunc ℚ) - 1) ^ 2 * Φ (c.derivative * d - c * d.derivative)
      = -(2 * (Φ d) ^ 2 * ((RatFunc.X : RatFunc ℚ) - 2) ^ 2) := by
    rw [add_eq_zero_iff_eq_neg] at hR
    exact hR
  have hN : Φ (c.derivative * d - c * d.derivative)
      = (-(2 * (Φ d) ^ 2 * ((RatFunc.X : RatFunc ℚ) - 2) ^ 2))
          * (((RatFunc.X : RatFunc ℚ) - 1) ^ 2)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hA]
    rw [mul_comm, hvanish]
  rw [hN]
  field_simp

end Work.C7
