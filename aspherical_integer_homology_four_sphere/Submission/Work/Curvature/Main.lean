import Submission.Work.Curvature.Basic
import Submission.Work.Curvature.Deriv
import Submission.Work.Curvature.UHS
import Submission.Work.Curvature.warpedMetric_chrWarped_koszul
import Submission.Work.Curvature.warpedMetric_dBmodel
import Submission.Work.Curvature.flat_sec
import Submission.Work.Curvature.warped_sec_nonpos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The curvature chapter: summary and main results

`Submission/Work/Curvature/` computes the Riemann curvature of the three metric models out of which
the Ratcliffe–Tschantz manifold `M̂` is glued, in the coordinates of the blueprint
(`E4 = EuclideanSpace ℝ (Fin 4)`, `(r, θ, w₁, w₂)` with the height `s` of the upper half space
model as coordinate `3`).

## Interface

Everything is phrased for a *metric field* `G : MetricField = E4 → E4 → E4 → ℝ`:

* `uhsMetric q a b = (q 3)⁻¹ ^ 2 * ⟪a,b⟫`                          — upper half space (`s = q 3`);
* `warpedMetric f h q a b = diag(1, f(q 0)², h(q 0)², h(q 0)²)`    — filling region (`r = q 0`);
* `flatMetric h₀ q a b = diag(1, 1, h₀², h₀²)`                     — flat core.

`koszulChr G q a b` is the Christoffel symbol of `G` (the unique solution of the Koszul formula,
`koszulChr_eq_of_forall`), `dBmodel G q d a b` its derivative in the direction `d`, and
`modelCurv G q u v w` the coordinate vector of the curvature operator `R(∂_u, ∂_v) ∂_w`, in the
index order of the library's `Submission.ChartCurv.curvVec_eq_chart`.  Consequently
`G q (modelCurv G q u v v) u` is the sectional curvature numerator `⟨R(u,v)v, u⟩` in the sign
convention of `Submission.CurvatureVec`.

## Main results

| name | content |
|---|---|
| `uhs_sec` | `⟨R(u,v)v,u⟩ = −(g(u,u)g(v,v) − g(u,v)²)`, i.e. `K ≡ −1`, for `0 < q 3` |
| `uhs_sec_nonpos` | the same, in the form `≤ 0` |
| `warped_sec_eq` | `⟨R(u,v)v,u⟩ = −( f f'' (u₀v₁−u₁v₀)² + h h''[(u₀v₂−u₂v₀)²+(u₀v₃−u₃v₀)²] + f h f' h'[(u₁v₂−u₂v₁)²+(u₁v₃−u₃v₁)²] + h²h'²(u₂v₃−u₃v₂)² )` |
| `warped_sec_nonpos` | `⟨R(u,v)v,u⟩ ≤ 0` for `f,h > 0`, `f',h' ≥ 0`, `f'',h'' ≥ 0` at `r = q 0` |
| `flat_sec` | `modelCurv (flatMetric h₀) = 0` (the core is flat) |
| `flat_sec_nonpos` | the same, in the form `≤ 0` |

Supporting interface (all in `Work.Curvature`):

* `koszulRHS`, `koszulChr_spec`, `koszulChr_eq_of_forall`;
* `chrUHS`, `chrUHSvec`, `chrUHSderiv`, `koszulChr_uhsMetric`, `dBmodel_uhsMetric`,
  `modelCurv_uhsMetric`;
* `chrWarped`, `chrWarpedDeriv`, `koszulChr_warpedMetric`, `dBmodel_warpedMetric`,
  `modelCurv_warpedMetric`;
* `dG_uhsMetric`, `dG_warpedMetric`, `dG_flatMetric` (the metric derivatives);
* positivity: `uhsMetric_pos`, `warpedMetric_pos`, `warpedMetric_pos'`, `flatMetric_pos`.

See `NOTES.md` for the conventions, the derivation of the formulas and the status of Part 2 (the
bridge to the Cartan–Hadamard machinery, which needs the `LC` area).
-/

open scoped RealInnerProductSpace
open Filter Topology
open Classical

namespace Work.Curvature

noncomputable section

/-- **The flat core has non-positive sectional curvature** (it is flat). -/
theorem flat_sec_nonpos (h₀ : ℝ) (h0 : h₀ ≠ 0) (q u v : E4) :
    flatMetric h₀ q (modelCurv (flatMetric h₀) q u v v) u ≤ 0 := by
  rw [flat_sec h₀ h0 q u v v]
  simp

/-! ## The three models have non-positive sectional curvature, in the `SecNonposAt` form -/

/-- The upper half space model has non-positive curvature on `{q 3 > 0}`. -/
theorem secNonposAt_uhs (q : E4) (hq : 0 < q 3) : SecNonposAt uhsMetric q :=
  fun u v => uhs_sec_nonpos q hq u v

/-- The flat core is flat. -/
theorem secNonposAt_flat (h₀ : ℝ) (h0 : h₀ ≠ 0) (q : E4) : SecNonposAt (flatMetric h₀) q :=
  fun u v => flat_sec_nonpos h₀ h0 q u v

/-- The warped filling model has non-positive curvature as soon as the warping functions are
positive, nondecreasing and convex at `r = q 0`. -/
theorem secNonposAt_warped (f h : ℝ → ℝ) (q : E4)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h)
    (hf0 : 0 < f (q 0)) (hh0 : 0 < h (q 0))
    (hf1 : 0 ≤ deriv f (q 0)) (hh1 : 0 ≤ deriv h (q 0))
    (hf2 : 0 ≤ deriv^[2] f (q 0)) (hh2 : 0 ≤ deriv^[2] h (q 0)) :
    SecNonposAt (warpedMetric f h) q :=
  fun u v => warped_sec_nonpos f h q u v hf hh hf0 hh0 hf1 hh1 hf2 hh2

end

end Work.Curvature
