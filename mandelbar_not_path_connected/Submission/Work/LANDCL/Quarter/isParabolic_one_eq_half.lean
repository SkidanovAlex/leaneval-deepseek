import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LANDCL.Deriv.tsq_deriv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The only parabolic fixed point of `T̄_{1/4}` is the cusp `1/2`

At `c = 1/4` the map `T̄_c(z) = z̄² + c` has exactly three fixed points, `1/2` and
`-1/2 ± i`; the multiplier of the holomorphic second return map `Tsq c` at the latter two is
`5`, while at `1/2` it is `1`.  Hence a point that is simultaneously fixed and of parabolic
multiplier `1` must be `1/2`.

The proof below derives this algebraically.  From the fixed point equation
`z̄² + 1/4 = z` and the multiplier equation `4 z (z² + 1/4) = 1` (the derivative of `Tsq`), one
first gets `z·z̄ = 1/4` (conjugating the fixed point equation gives `z² + 1/4 = z̄`), and then
that the "trace" `s = z + z̄` satisfies `s² = s`.  In the branch `s = 0` one has `z̄ = -z`,
forcing `z² = -1/4` and then `z = 0`, contradicting `z·z̄ = 1/4`; in the branch `s = 1` the
identity `(z - 1/2)² = z² - (z + z̄) z + z z̄` gives `(z - 1/2)² = 0`, i.e. `z = 1/2`.
-/

namespace Work.LANDCL.Quarter

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The only parabolic fixed point of `T̄_{1/4}` is the cusp `1/2`.** -/
theorem isParabolic_one_eq_half {z : ℂ}
    (h : Work.Landing.IsParabolic (1 / 4 : ℂ) 1 z) : z = 1 / 2 := by
  obtain ⟨⟨_, hper⟩, hmult⟩ := h
  simp only [Function.iterate_one] at hper
  -- fixed point equation
  have hz : star z ^ 2 + 1 / 4 = z := by simpa using hper
  -- multiplier equation: `deriv (Tsq (1/4)) z = 1`
  have hderiv : 4 * z * (z ^ 2 + 1 / 4) = 1 := by
    have h1 : deriv (Work.Landing.Tsq (1 / 4 : ℂ)) z = 1 := by
      simpa [Work.Landing.multiplier2, Function.iterate_one] using hmult
    rw [Work.LANDCL.Deriv.tsq_deriv] at h1
    simpa using h1
  -- conjugate fixed point equation
  have hconj : z ^ 2 + 1 / 4 = star z := by
    simpa using congrArg star hz
  -- the product `z z̄ = 1/4`
  have hprod : z * star z = 1 / 4 := by
    have h1 : 4 * z * star z = 1 := by
      rw [hconj] at hderiv; exact hderiv
    linear_combination (1 / 4 : ℂ) * h1
  -- the trace `s = z + z̄` satisfies `s² = s`
  have hs : (z + star z) ^ 2 = z + star z := by
    linear_combination hz + hconj + 2 * hprod
  have hs' : (z + star z) * (z + star z - 1) = 0 := by
    have h := hs
    rw [pow_two] at h
    rw [mul_sub, mul_one, sub_eq_zero]
    exact h
  rcases mul_eq_zero.mp hs' with h0 | h1
  · -- `z + z̄ = 0`: then `z² = -1/4` and `z = 0`, against `z z̄ = 1/4`.
    have hw : star z = -z := by linear_combination h0
    have hz2 : z ^ 2 = -1 / 4 := by
      have hh := hprod
      rw [hw] at hh
      linear_combination (-1 : ℂ) * hh
    have hz0 : z = 0 := by
      have hh := hconj
      rw [hw] at hh
      linear_combination hh - hz2
    rw [hz0] at hprod
    norm_num at hprod
  · -- `z + z̄ = 1`: then `(z - 1/2)² = z² - (z + z̄) z + z z̄ = 0`, so `z = 1/2`.
    have hsq : (z - 1 / 2) ^ 2 = 0 := by
      linear_combination z * h1 - hprod
    have hz2 : z - 1 / 2 = 0 := by
      have h := hsq
      rw [pow_two] at h
      exact mul_self_eq_zero.mp h
    linear_combination hz2

end Work.LANDCL.Quarter
