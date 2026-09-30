import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `cuspX` recovers a cusp coordinate from `outerU` and `outerY`

The cusp coordinate of `Basic` is

`cuspX v u y = u • σ_v + y₂ • κ_{v,2} + y₃ • κ_{v,3}`,  `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}`,

an `ℝ`-linear isomorphism `ℝ × ℝ² → ℝ³` because `(κ_{v,1}, κ_{v,2}, κ_{v,3})` is an orthogonal
basis of `ℝ³` (data file `Data.lean`) and the slope has `c_v = 0`, so that the change of basis
`(κ_{v,1}, κ_{v,2}) ↦ (σ_v, κ_{v,2})` is triangular with unit diagonal.

`outerU v x` and `outerY v x` are the explicit inverse of that map: `outerU` is the `κ_{v,1}`
coefficient of `x` and `outerY` is the pair of *new* coefficients of `x` in the basis
`(σ_v, κ_{v,2}, κ_{v,3})`, i.e.

`x = outerU v x • σ_v + (outerY v x) 0 • κ_{v,2} + (outerY v x) 1 • κ_{v,3}`.

This file proves exactly that, and hence `cuspX v (outerU v x) (outerY v x) = x`.

The two ingredients are

* `kappaCoord_expansion`: the `κ`-coordinates `⟪x,κ_{v,i}⟫/‖κ_{v,i}‖²` of `x` recompose `x` — the
  statement that `(κ_{v,1}, κ_{v,2}, κ_{v,3})` spans `ℝ³` as an orthogonal family;
* `slopeC_zero`: the data takes `c_v = 0` for all five cusps (`Data.slopeC`), so that the slope
  acquires no `κ_{v,3}`-component and the coordinate change is triangular.
-/

noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- The squared norm of a vector of `ℝ³` in coordinates: `‖(a,b,c)‖² = a² + b² + c²`. -/
private lemma norm_sq_piLp3 (a b c : ℝ) : ‖(!₂[a,b,c] : E3)‖ ^ 2 = a^2 + b^2 + c^2 := by
  rw [PiLp.norm_eq_of_L2, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-- **The `κ`-coordinates of a cusp coordinate `x` recompose `x`.**  The three lattice vectors
`κ_{v,1}, κ_{v,2}, κ_{v,3}` are pairwise orthogonal and nonzero (`kv_ne_zero`, `kappa_orthogonal`),
and they lie in the three-dimensional space `ℝ³`, so they form an orthogonal basis of `ℝ³`
(`Data.kappa` even exhibits each of them as a scalar multiple of a distinct standard basis vector):
`x = ∑ᵢ (⟪x,κ_{v,i}⟫/‖κ_{v,i}‖²) κ_{v,i}`. -/
lemma kappaCoord_expansion (v : Fin 5) (x : E3) :
    kappaCoord v 0 x • kv v 0 + kappaCoord v 1 x • kv v 1 + kappaCoord v 2 x • kv v 2 = x := by
  fin_cases v <;>
    ext j <;> fin_cases j <;>
    simp [kv, kappa, kappaCoord, PiLp.inner_apply, Fin.sum_univ_three, norm_sq_piLp3] <;>
    ring

/-- The data takes `c_v = 0` for every cusp (`Data.slopeC`): the slope `σ_v` lies in the
coordinate plane of `κ_{v,1}, κ_{v,2}`. -/
private lemma slopeC_zero (v : Fin 5) : slopeC v = 0 := by fin_cases v <;> rfl

/-- The defining property of `outerU` and `outerY`: they are the coordinates of `x` in the basis
`(σ_v, κ_{v,2}, κ_{v,3})` of `ℝ³`.  Indeed `σ_v = κ_{v,1} + b_v κ_{v,2}` (as `c_v = 0`), so
`outerU v x • σ_v + (outerY v x) 0 • κ_{v,2} + (outerY v x) 1 • κ_{v,3}` expands to
`(⟪x,κ_{v,1}⟫/‖κ_{v,1}‖²) κ_{v,1} + (⟪x,κ_{v,2}⟫/‖κ_{v,2}‖²) κ_{v,2}
 + (⟪x,κ_{v,3}⟫/‖κ_{v,3}‖²) κ_{v,3}`, which is `x` by `kappaCoord_expansion`. -/
private lemma cuspX_outerU_outerY_aux (v : Fin 5) (x : E3) :
    cuspX v (outerU v x) (outerY v x)
      = kappaCoord v 0 x • kv v 0 + kappaCoord v 1 x • kv v 1 + kappaCoord v 2 x • kv v 2 := by
  simp only [cuspX, cuspY, outerU, outerY, Work.Cusp.slope, slopeC_zero, lam2, lam3,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  module

/-- **The outer chart data of a cusp coordinate recovers it: `cuspX` is a retraction of
`(outerU, outerY)`.**  `outerU v x` is the meridian (perimeter) coordinate of `x` and `outerY v x`
the two torus (phase) coordinates, and `cuspX v` reassembles the UHS cube coordinate
`x = u σ_v + y₂ λ_{v,2} + y₃ λ_{v,3}` from them. -/
theorem cuspX_outerU_outerY (v : Fin 5) (x : E3) : cuspX v (outerU v x) (outerY v x) = x := by
  rw [cuspX_outerU_outerY_aux v x, kappaCoord_expansion v x]

end Work.Cusp
