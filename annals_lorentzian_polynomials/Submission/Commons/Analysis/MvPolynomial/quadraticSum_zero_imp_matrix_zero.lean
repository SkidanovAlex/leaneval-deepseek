import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace Commons.Analysis.MvPolynomial

open scoped BigOperators

set_option autoImplicit false

/-- If the quadratic polynomial `sum_uv (A u v) * X_u * X_v` with a SYMMETRIC real
coefficient matrix `A` is the zero polynomial, then `A = 0`.
Suggested proof: evaluate the quadratic polynomial (equivalently, compare coefficients,
or take the total second derivative `pderiv a (pderiv b ...)` at the origin) at the
Kronecker-delta points to recover each entry: the coefficient of `X_a * X_a` equals
`A a a`, and for `a ≠ b` the coefficient of `X_a * X_b` equals `A a b + A b a`, which
vanishes by symmetry only when `A a b = 0`. -/
theorem quadraticSum_zero_imp_matrix_zero (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm)
    (h0 : (∑ u : Fin n, ∑ v : Fin n, MvPolynomial.C (A u v) * MvPolynomial.X u * MvPolynomial.X v) = 0) :
    A = 0 := by
  -- Evaluating the quadratic polynomial at any point yields the corresponding
  -- quadratic form, which therefore vanishes identically.
  have hquad : ∀ x : Fin n → ℝ,
      (∑ u : Fin n, ∑ v : Fin n, A u v * x u * x v) = 0 := by
    intro x
    have hx := congrArg (MvPolynomial.eval x) h0
    have hcalc : MvPolynomial.eval x (∑ u : Fin n, ∑ v : Fin n,
        MvPolynomial.C (A u v) * MvPolynomial.X u * MvPolynomial.X v)
        = ∑ u : Fin n, ∑ v : Fin n, A u v * x u * x v := by
      simp [map_sum, map_mul]
    simpa [hcalc] using hx
  -- Symmetry of `A` entrywise.
  have hsymm : ∀ a b : Fin n, A a b = A b a := by
    intro a b
    unfold Matrix.IsSymm at hA
    have hh := congrFun (congrFun hA a) b
    simpa [Matrix.transpose_apply] using hh.symm
  -- Diagonal entries vanish: evaluate at the Kronecker-delta point concentrated at `a`.
  have hdiag : ∀ a : Fin n, A a a = 0 := by
    intro a
    have hx := hquad (fun u : Fin n => if u = a then (1 : ℝ) else 0)
    simpa [Finset.sum_ite_eq'] using hx
  -- Off-diagonal entries vanish: evaluate at the sum of the two delta points.
  have hoff : ∀ {a b : Fin n}, a ≠ b → A a b = 0 := by
    intro a b hab
    have hx := hquad (fun u : Fin n => (if u = a then (1 : ℝ) else 0) + (if u = b then 1 else 0))
    have hval :
        (∑ u : Fin n, ∑ v : Fin n,
          A u v * ((if u = a then (1 : ℝ) else 0) + (if u = b then 1 else 0)) *
            ((if v = a then 1 else 0) + (if v = b then 1 else 0)))
          = A a a + A a b + A b a + A b b := by
      simp [mul_add, Finset.sum_add_distrib, Finset.sum_ite_eq']
      ring
    have hx' : A a a + A a b + A b a + A b b = 0 := by
      simpa [hval] using hx
    have hsum : A a b + A b a = 0 := by
      nlinarith [hx', hdiag a, hdiag b]
    have htwo : (2 : ℝ) * A a b = 0 := by
      nlinarith [hsum, hsymm a b]
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  -- Every entry is zero.
  ext a b
  by_cases h : a = b
  · subst h
    exact hdiag a
  · exact hoff h

end Commons.Analysis.MvPolynomial