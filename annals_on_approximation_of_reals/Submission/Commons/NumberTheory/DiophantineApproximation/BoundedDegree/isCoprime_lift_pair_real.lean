import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial

/-- If a polynomial `p` over a field does not vanish at `a`, then the linear
polynomial `X - C a` is coprime with `p`. -/
private lemma X_sub_C_isCoprime_eval_ne_zero {K : Type*} [Field K] (p : K[X]) (a : K)
    (hp : p.eval a ≠ 0) : IsCoprime (X - C a) p := by
  rcases (EuclideanDomain.dvd_or_coprime (X - C a) p (irreducible_X_sub_C a)) with hd | hc
  · exfalso
    exact hp (dvd_iff_isRoot.mp hd)
  · exact hc

/-- Coprimality is preserved when two coprime real polynomials are multiplied by
`(X - lam)`-powers on different sides, provided the `lam`'s avoid the roots of the
partner polynomial and are distinct: `A0(a) ≠ 0`, `A1(b) ≠ 0`, `a ≠ b`. -/
theorem isCoprime_lift_pair_real (A0 A1 : Polynomial ℝ) (h : IsCoprime A0 A1)
    (a0 a1 : ℕ) (lam0 lam1 : ℝ) (hne0 : A1.eval lam0 ≠ 0) (hne1 : A0.eval lam1 ≠ 0)
    (hlam : lam0 ≠ lam1) :
    IsCoprime (((Polynomial.X - Polynomial.C lam0) ^ a0) * A0)
      (((Polynomial.X - Polynomial.C lam1) ^ a1) * A1) := by
  -- `X - C lam0` is coprime with `A1`, hence so is its `a0`-th power.
  have h1b : IsCoprime ((X - C lam0) ^ a0) A1 :=
    (X_sub_C_isCoprime_eval_ne_zero A1 lam0 hne0).pow_left
  -- `A0` is coprime with `X - C lam1`, hence also with its `a1`-th power.
  have h2b : IsCoprime A0 ((X - C lam1) ^ a1) :=
    (X_sub_C_isCoprime_eval_ne_zero A0 lam1 hne1).symm.pow_right
  -- the two linear factors are coprime because `lam0 ≠ lam1`.
  have h3b : IsCoprime ((X - C lam0) ^ a0) ((X - C lam1) ^ a1) :=
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hlam).isUnit).pow
  -- `(X - C lam0) ^ a0` is coprime with the whole second product
  have hstep1 : IsCoprime ((X - C lam0) ^ a0) (((X - C lam1) ^ a1) * A1) :=
    h3b.mul_right h1b
  -- and so is `A0`
  have hstep2 : IsCoprime A0 (((X - C lam1) ^ a1) * A1) :=
    h2b.mul_right h
  exact hstep1.mul_left hstep2

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree