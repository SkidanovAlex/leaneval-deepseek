import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- Iterated formal derivative along a substitution `X ↦ P` whose derivative is the constant
`a`: it pulls out the scalar `a ^ n`.  This is the chain rule iterated for a constant-derivative
inner polynomial. -/
private lemma iterate_derivative_comp_of_derivative_eq_C (q P : Polynomial ℂ) (a : ℂ)
    (hP : Polynomial.derivative P = Polynomial.C a) (n : ℕ) :
    Polynomial.derivative^[n] (q.comp P) =
      Polynomial.C (a ^ n) * (Polynomial.derivative^[n] q).comp P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp, hP,
      ← Function.iterate_succ_apply' (f := Polynomial.derivative) (n := n) (x := q),
      ← mul_assoc, ← map_mul, ← pow_succ]

/-- The Hasse derivative along an affine substitution `X ↦ aX + c`: it commutes with the
substitution up to the scalar `a^n`. -/
theorem yc_hasseDeriv_comp_affine (q : Polynomial ℂ) (a c : ℂ) (n : ℕ) :
    Polynomial.hasseDeriv n (q.comp (Polynomial.C a * Polynomial.X + Polynomial.C c))
      = Polynomial.C (a ^ n) *
        (Polynomial.hasseDeriv n q).comp (Polynomial.C a * Polynomial.X + Polynomial.C c) := by
  have hP : Polynomial.derivative (Polynomial.C a * Polynomial.X + Polynomial.C c)
      = Polynomial.C a := by simp
  have hg := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) n)
    (q.comp (Polynomial.C a * Polynomial.X + Polynomial.C c))
  have hq := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) n) q
  have hg' : n.factorial • Polynomial.hasseDeriv n
        (q.comp (Polynomial.C a * Polynomial.X + Polynomial.C c))
      = Polynomial.derivative^[n] (q.comp (Polynomial.C a * Polynomial.X + Polynomial.C c)) := hg
  have hq' : n.factorial • Polynomial.hasseDeriv n q = Polynomial.derivative^[n] q := hq
  have hLHS : Polynomial.C ((n.factorial : ℕ) : ℂ) *
        Polynomial.hasseDeriv n (q.comp (Polynomial.C a * Polynomial.X + Polynomial.C c))
      = Polynomial.C (a ^ n) *
        (Polynomial.derivative^[n] q).comp (Polynomial.C a * Polynomial.X + Polynomial.C c) := by
    rw [Polynomial.C_eq_natCast, ← nsmul_eq_mul, hg',
      iterate_derivative_comp_of_derivative_eq_C q
        (Polynomial.C a * Polynomial.X + Polynomial.C c) a hP n]
  have hRHS : Polynomial.C ((n.factorial : ℕ) : ℂ) *
        (Polynomial.C (a ^ n) *
          (Polynomial.hasseDeriv n q).comp (Polynomial.C a * Polynomial.X + Polynomial.C c))
      = Polynomial.C (a ^ n) *
        (Polynomial.derivative^[n] q).comp (Polynomial.C a * Polynomial.X + Polynomial.C c) := by
    have hfacq : Polynomial.C ((n.factorial : ℕ) : ℂ) * Polynomial.hasseDeriv n q
        = Polynomial.derivative^[n] q := by
      rw [Polynomial.C_eq_natCast, ← nsmul_eq_mul, hq']
    rw [mul_left_comm, ← Polynomial.C_mul_comp, hfacq]
  exact mul_left_cancel₀ (Polynomial.C_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))
    (hLHS.trans hRHS.symm)

end Work.BW
