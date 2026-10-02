import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.ParamAngle

/-- A purely combinatorial fact about iterates of a self-map `f`: if `f^[n] x = x` but
`x` is not a fixed point of `f`, then no point of the orbit segment `x, f x, …, f^[n-1] x`
is a fixed point of `f`.

Indeed, if `f (f^[j] x) = f^[j] x` for some `j < n`, then applying `f^[n-(j+1)]` to both
sides yields `f^[n] x = f^[n-1] x`, so `x = f^[n-1] x` and hence `f x = f^[n] x = x`,
contradicting `f x ≠ x`. -/
theorem iterate_succ_ne_of_period {α : Type*} (f : α → α) {x : α} {n : ℕ}
    (hn : f^[n] x = x) (hne : f x ≠ x) (j : ℕ) (hj : j < n) :
    f (f^[j] x) ≠ f^[j] x := by
  intro h
  have hj1 : j + 1 ≤ n := by omega
  have h1 : f^[n] x = f^[(n - (j + 1)) + (j + 1)] x :=
    congrArg (fun m => f^[m] x) (by omega)
  have inner : f^[j + 1] x = f^[j] x :=
    (Function.iterate_succ_apply' f j x).trans h
  have h2 : f^[(n - (j + 1)) + (j + 1)] x = f^[(n - (j + 1)) + j] x :=
    (Function.iterate_add_apply f (n - (j + 1)) (j + 1) x).trans
      ((congrArg (fun y => f^[n - (j + 1)] y) inner).trans
        (Function.iterate_add_apply f (n - (j + 1)) j x).symm)
  have h3 : f^[(n - (j + 1)) + j] x = f^[n - 1] x :=
    congrArg (fun m => f^[m] x) (by omega)
  have hx : x = f^[n - 1] x := by
    have key : f^[n] x = f^[n - 1] x := h1.trans (h2.trans h3)
    rw [hn] at key
    exact key
  have hfx : f x = f^[n] x := by
    have h4 : f x = f (f^[n - 1] x) := congrArg f hx
    rw [h4, ← Function.iterate_succ_apply' f (n - 1) x]
    rw [show (n - 1).succ = n by omega]
  exact hne (hfx.trans hn)

/-- A point of exact period `5` under the antiholomorphic quadratic map `Tantibar c`
is not fixed by any of its first five iterates. -/
theorem cycle_mem_ne_fixed (c z₁ : ℂ)
    (h5 : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁)
    (hne : LeanEval.ComplexAnalysis.Tantibar c z₁ ≠ z₁) (j : ℕ) (hj : j < 5) :
    LeanEval.ComplexAnalysis.Tantibar c ((LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁) ≠
      (LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁ :=
  iterate_succ_ne_of_period (LeanEval.ComplexAnalysis.Tantibar c) h5 hne j hj

end Work.LANDCL.ParamAngle
