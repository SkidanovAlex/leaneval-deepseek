import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.ParamRays.Interface
import Submission.Work.Landing.Land.Caratheodory
import Submission.Work.LandLeaves.exists_ball_iterate_norm_sub_lt
import Submission.Work.LandLeaves.boundedOrbit_of_ball

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Attracting cycles of `T_c` lie in the interior of the filled Julia set

This file proves the geometric input `Work.Landing.AttractingCyclesInner` of the landing theorem
for the tricorn `T_c(z) = z̄² + c` (Milnor 18.10, ledger item 3 of
`Submission/Work/LandLeaves/Defs.lean`):

> every attracting periodic point `z` of `T_c` has a neighbourhood consisting of
> points whose orbit is bounded, i.e. of *non-escaping* points.

Since the escaping set is the complement of the filled Julia set
(`Work.ParamRays.escaping_iff_not_bounded`), this says exactly that the basin of an attracting
cycle lies inside the filled Julia set, so that the only unbounded Fatou component is the basin
of infinity.

## The argument

Fix an attracting point `z`: `z` is periodic of some period `k > 0` for the antiholomorphic
`T_c` and the multiplier of the *holomorphic* second return map
`Tsq c = T_c ∘ T_c` satisfies `‖deriv ((Tsq c)^[k]) z‖ < 1` (`Work.Landing.multiplier2`).
Write `F = (Tsq c)^[k] = (T_c)^[2k]` (`Tsq_iterate_eq_Tantibar` below), a *holomorphic*
polynomial map with the attracting fixed point `z`.  By the elementary local estimate
`Work.LandLeaves.exists_ball_iterate_norm_sub_lt` some ball `B(z,r)` is carried strictly into
itself by `F`, hence every `F`-iterate of a point `w` of the ball stays within distance `r` of
`z`.  Reading the `T_c`-orbit of `w` in the subsequence of indices divisible by `2k` (which is
the `F`-orbit) and filling in the at most `2k - 1` intermediate indices
(`Work.LandLeaves.boundedOrbit_of_ball`), the whole `T_c`-orbit of `w` is bounded — i.e. `w` is
not an escaping point, and `B(z,r)` is the required neighbourhood.

## Main result

* `Work.LandLeaves.attractingCyclesInner` : `Work.Landing.AttractingCyclesInner c` for every
  `c : ℂ`.
-/

namespace Work.LandLeaves

open Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- `(Tsq c)^[k] = (T_c)^[2k]`: the `k`-th iterate of the holomorphic second return map is the
`2k`-th iterate of the antiholomorphic map. -/
private theorem Tsq_iterate_eq_Tantibar (c : ℂ) (k : ℕ) :
    (Work.Landing.Tsq c)^[k] = (Tantibar c)^[2 * k] := by
  rw [Tsq_eq_iterate_two, Function.iterate_mul]

/-- The `k`-th iterate of the polynomial `Tsq c` is (complex) differentiable. -/
private theorem differentiable_Tsq_iterate (c : ℂ) (k : ℕ) :
    Differentiable ℂ ((Work.Landing.Tsq c)^[k]) := by
  have h1 : Differentiable ℂ (Work.Landing.Tsq c) := by
    rw [show Work.Landing.Tsq c = (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c) from rfl]
    fun_prop
  exact h1.iterate k

/-- A periodic point `z` of `T_c` of period `k` is a fixed point of the holomorphic second
return map `(Tsq c)^[k] = (T_c)^[2k]`. -/
private theorem Tsq_iterate_apply_of_periodic {c z : ℂ} {k : ℕ}
    (hper : Work.Landing.PeriodicPoint (Tantibar c) k z) :
    ((Work.Landing.Tsq c)^[k]) z = z := by
  rw [Tsq_iterate_eq_Tantibar]
  rw [show 2 * k = k * 2 from by omega, Function.iterate_mul]
  exact (show Function.IsFixedPt ((Tantibar c)^[k]) z from hper.2).iterate 2

/-- **Attracting cycles of the tricorn are not on the boundary of the filled Julia set.**

For every `c : ℂ`, every attracting periodic point `z` of `T_c` has a neighbourhood whose points
do not escape: the local basin of attraction of the cycle is contained in the filled Julia set.
This is the geometric input of the landing theorem (Milnor 18.10). -/
theorem attractingCyclesInner (c : ℂ) : Work.Landing.AttractingCyclesInner c := by
  rintro z ⟨k, hper, hmult⟩
  -- the holomorphic second return map at `z` is a contraction there
  obtain ⟨r, hr, hball⟩ := exists_ball_iterate_norm_sub_lt
    (f := (Work.Landing.Tsq c)^[k]) (f' := deriv ((Work.Landing.Tsq c)^[k]) z)
    ((differentiable_Tsq_iterate c k).differentiableAt.hasDerivAt)
    (Tsq_iterate_apply_of_periodic hper) hmult
  refine ⟨r, hr, fun w hw => ?_⟩
  show ¬ Work.ParamRays.Escaping c w
  intro hesc
  rw [Work.ParamRays.escaping_iff_not_bounded] at hesc
  exact hesc (boundedOrbit_of_ball hper.1 (fun m => hball w hw m))

end Work.LandLeaves
