import Submission.Work.RiemLib.Commons.Analysis.Calculus.hasDerivAt_deriv_partial_swap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.Calculus

/-- Symmetry of the mixed partial derivatives in the one-variable `deriv` form:
if `F : ℝ × ℝ → E` is `C²` at `(x, y)`, then `∂/∂t (∂F/∂s)` and `∂/∂s (∂F/∂t)`
agree at `(x, y)`. -/
theorem deriv_deriv_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {x y : ℝ} (hF : ContDiffAt ℝ 2 F (x, y)) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => F (s, t)) x) y
      = deriv (fun s : ℝ => deriv (fun t : ℝ => F (s, t)) y) x := by
  have h := hasDerivAt_deriv_partial_swap (F := F) (s₀ := x) (t₀ := y) hF
  exact h.deriv.symm

end Commons.Analysis.Calculus
