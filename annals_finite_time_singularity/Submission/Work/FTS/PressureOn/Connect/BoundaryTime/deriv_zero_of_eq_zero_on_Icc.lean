import Mathlib.Analysis.Calculus.Deriv.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect.BoundaryTime

theorem deriv_zero_of_eq_zero_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {S t : ℝ} (hS : 0 < S) (hg : ∀ s ∈ Set.Icc 0 S, g s = 0)
    (ht : t ∈ Set.Icc 0 S) : deriv g t = 0 := by
  -- On the interval `Icc 0 S` the function `g` agrees with the constant `0`, so it has the
  -- one-sided (within `Icc 0 S`) derivative `0` at every point of the interval.  Since
  -- `Icc 0 S` is a convex set with nonempty interior (as `0 < S`), it is a set of unique
  -- differentiability, so the two-sided derivative `deriv g t` must equal that one-sided
  -- derivative.  (This covers the endpoints `t = 0` and `t = S` as well: `deriv` is the
  -- two-sided derivative, and if it exists it agrees with the one within the interval.)
  exact HasDerivWithinAt.deriv_eq_zero
    ((hasDerivWithinAt_const (x := t) (s := Set.Icc 0 S) (c := (0 : E))).congr
      hg (hg t ht))
    ((uniqueDiffOn_Icc hS).uniqueDiffWithinAt ht)

end Work.FTS.PressureOn.Connect.BoundaryTime
