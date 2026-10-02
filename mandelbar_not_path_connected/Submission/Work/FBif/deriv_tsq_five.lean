import Mathlib
import Submission.Work.FBif.IterPoly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- **`(Tsq c)^[5]` is the holomorphic polynomial of the tenth iterate, with its two derivatives.**

`Work.Landing.Tsq c = (T_c) ∘ (T_c) = fun z => (z ^ 2 + star c) ^ 2 + c` is the holomorphic
second iterate of `T_c`, so `(Tsq c)^[5] = (T_c)^[10] = Work.EL.F c`.  Hence for every `z : ℂ`,
`deriv ((Tsq c)^[5]) z = (iterP c 10).derivative.eval z` and
`iteratedDeriv 2 ((Tsq c)^[5]) z = (iterP c 10).derivative.derivative.eval z`.

Suggested route.  `Work.Landing.Tsq c = Tantibar c ∘ Tantibar c` by `funext` and `ring`; hence
`(Tsq c)^[5] = ((Tantibar c)^[2])^[5] = (Tantibar c)^[10]` (`Function.iterate_mul`), and
`(Tantibar c)^[10] = fun z => (iterP c 10).eval z` by `Work.FBif.iterP_ten_eval` and
`funext`.  Then use `Polynomial.deriv` (`deriv (fun z => P.eval z) = fun z => P.derivative.eval z`)
and `iteratedDeriv 2 f = deriv (deriv f)`. -/
theorem deriv_tsq_five (c z : ℂ) :
    deriv ((Work.Landing.Tsq c)^[5]) z = (Work.FBif.iterP c 10).derivative.eval z ∧
    iteratedDeriv 2 ((Work.Landing.Tsq c)^[5]) z =
      (Work.FBif.iterP c 10).derivative.derivative.eval z := by
  -- `Tsq c` is the composite `T_c ∘ T_c` of the antiholomorphic quadratic with itself.
  have hcomp : (LeanEval.ComplexAnalysis.Tantibar c) ∘ (LeanEval.ComplexAnalysis.Tantibar c)
      = Work.Landing.Tsq c := by
    funext w
    simp only [Function.comp_apply, LeanEval.ComplexAnalysis.Tantibar, Work.Landing.Tsq,
      starRingEnd_apply, star_add, star_pow, star_star]
  -- hence `(Tsq c) = (T_c)^[2]` as functions.
  have h2 : (LeanEval.ComplexAnalysis.Tantibar c)^[2] = Work.Landing.Tsq c := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ, Function.iterate_one]
    exact hcomp
  -- and therefore `(T_c)^[10] = (Tsq c)^[5]`.
  have hten : (LeanEval.ComplexAnalysis.Tantibar c)^[10] = (Work.Landing.Tsq c)^[5] := by
    have h := Function.iterate_mul (LeanEval.ComplexAnalysis.Tantibar c) 2 5
    rw [show (10 : ℕ) = 2 * 5 from rfl, h, h2]
  -- `(Tsq c)^[5]` is the evaluation of the polynomial of the tenth iterate.
  have hfun : (Work.Landing.Tsq c)^[5] = fun w => (Work.FBif.iterP c 10).eval w := by
    funext w
    rw [← hten]
    exact (Work.FBif.iterP_ten_eval c w).symm
  -- first derivative
  have hd : deriv ((Work.Landing.Tsq c)^[5])
      = fun w => (Work.FBif.iterP c 10).derivative.eval w := by
    rw [hfun]
    funext w
    exact Polynomial.deriv (Work.FBif.iterP c 10)
  -- `iteratedDeriv 2 f = deriv (deriv f)`
  have hiter : iteratedDeriv (2 : ℕ) ((Work.Landing.Tsq c)^[5])
      = deriv (deriv ((Work.Landing.Tsq c)^[5])) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  constructor
  · rw [hd]
  · rw [hiter, hd]
    exact Polynomial.deriv ((Work.FBif.iterP c 10).derivative)

end Work.FBif
