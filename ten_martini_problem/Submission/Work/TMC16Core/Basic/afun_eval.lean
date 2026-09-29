/-
# Evaluation of the single-site bivariate polynomial `afun`

`Work.TMC16Core.Cheb.afun α lam E k j` is the potential
`E - 2λ cos(2π(x + jα - centre))` of the `j`-th site of the length-`k` window, written as
a bivariate polynomial in `X = cos 2πx` and `Y = sin 2πx`.  This file evaluates it:
substituting `X = cos 2πx`, `Y = sin 2πx` recovers the arithmetic almost Mathieu potential
`amoPot` at the translated phase `x - ctr k α`, site `j`.

The proof is the addition formula `cos(A+B) = cos A cos B - sin A sin B` applied to
`A = 2π(jα - ctr k α)`, `B = 2πx`, together with
`(x - ctr k α) + jα = jα - ctr k α + x`.
-/
import Mathlib
import Submission.Work.TMC16Core.Basic.pd_cheb_cont

namespace Work.TMC16Core.Basic

open Polynomial

/-- Evaluating the generic single-potential polynomial `cst P - cst a * (cst b * cX - cst c * sY)`
at `X = z`, `Y = y` gives `P - a * (b * z - c * y)`. -/
private lemma afun_eval_aux (P a b c y z : ℂ) :
    ((Work.TMC16Core.Cheb.cst P - Work.TMC16Core.Cheb.cst a *
        (Work.TMC16Core.Cheb.cst b * Work.TMC16Core.Cheb.cX -
         Work.TMC16Core.Cheb.cst c * Work.TMC16Core.Cheb.sY)).eval₂
        (Polynomial.evalRingHom z) y) = P - a * (b * z - c * y) := by
  simp only [Work.TMC16Core.Cheb.cst, Work.TMC16Core.Cheb.cX, Work.TMC16Core.Cheb.sY,
    Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  simp

theorem afun_eval (α lam : ℝ) (E : ℂ) (k j : ℕ) (x : ℝ) :
    (Work.TMC16Core.Cheb.afun α lam E k j).eval₂
        (Polynomial.evalRingHom (((Real.cos (2 * Real.pi * x) : ℝ)) : ℂ))
        (((Real.sin (2 * Real.pi * x) : ℝ)) : ℂ)
      = E - ((Work.TMC16Core.amoPot α lam (x - Work.TMC16Core.Cheb.ctr k α) ((j : ℕ) : ℤ) : ℝ) : ℂ) := by
  have hcos : Real.cos (2 * Real.pi * ((x - Work.TMC16Core.Cheb.ctr k α) + (j : ℝ) * α))
      = Real.cos (2 * Real.pi * ((j : ℝ) * α - Work.TMC16Core.Cheb.ctr k α)) * Real.cos (2 * Real.pi * x)
        - Real.sin (2 * Real.pi * ((j : ℝ) * α - Work.TMC16Core.Cheb.ctr k α)) * Real.sin (2 * Real.pi * x) := by
    have h : 2 * Real.pi * ((x - Work.TMC16Core.Cheb.ctr k α) + (j : ℝ) * α)
        = 2 * Real.pi * ((j : ℝ) * α - Work.TMC16Core.Cheb.ctr k α) + 2 * Real.pi * x := by ring
    rw [h, Real.cos_add]
  simp only [Work.TMC16Core.Cheb.afun, Work.TMC16Core.amoPot]
  rw [show (((j : ℕ) : ℤ) : ℝ) = (j : ℝ) from by norm_num]
  rw [hcos]
  rw [afun_eval_aux]
  push_cast
  ring

end Work.TMC16Core.Basic
