import Mathlib
import Submission.Work.Curvature.Basic
import Submission.Work.Curvature.Deriv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Flatness of the model flat metric

The metric `flatMetric h₀ = diag(1, 1, h₀², h₀²)` is independent of the point
`q`, so all of its metric derivatives `dG (flatMetric h₀) q v a c` vanish
(`dG_flatMetric`).  Consequently:

* the Koszul right hand side `koszulRHS (flatMetric h₀) q a b c` vanishes
  (`koszulRHS_flatMetric`);
* the Christoffel symbols `koszulChr (flatMetric h₀) q a b` vanish
  (`koszulChr_flatMetric`) — the Koszul formula for the zero vector is satisfied
  by `0`, and `koszulChr_eq_of_forall` identifies the two;
* hence the derivative `dBmodel (flatMetric h₀) q d a b` of the Christoffel
  symbol vanishes (`dBmodel_flatMetric`).

The model curvature `modelCurv` is a combination of the two quantities above,
so it vanishes identically (`flat_sec`): the model metric is flat.
-/

open scoped RealInnerProductSpace
open Filter Topology
open Classical

namespace Work.Curvature

noncomputable section

/-- **The Koszul right hand side vanishes for the flat metric.**  Indeed every
metric derivative `dG (flatMetric h₀) q v a c` is zero. -/
theorem koszulRHS_flatMetric (h₀ : ℝ) (q a b c : E4) :
    koszulRHS (flatMetric h₀) q a b c = 0 := by
  rw [koszulRHS, dG_flatMetric, dG_flatMetric, dG_flatMetric]
  ring

/-- **The Christoffel symbols of the flat metric vanish.**  The zero vector solves
the Koszul formula, and `koszulChr_eq_of_forall` (whose hypotheses are
`flatMetric_sub_fst` and `flatMetric_pos`) identifies it with `koszulChr`. -/
theorem koszulChr_flatMetric (h₀ : ℝ) (h0 : h₀ ≠ 0) (q a b : E4) :
    koszulChr (flatMetric h₀) q a b = 0 := by
  refine koszulChr_eq_of_forall (flatMetric_sub_fst h₀ q) (flatMetric_pos h₀ h0 q) ?_
  intro c
  rw [koszulRHS_flatMetric]
  simp [flatMetric_apply]

/-- **The derivative of the flat Christoffel symbols vanishes.**  The function
`q' ↦ koszulChr (flatMetric h₀) q' a b` is constantly zero. -/
theorem dBmodel_flatMetric (h₀ : ℝ) (h0 : h₀ ≠ 0) (q d a b : E4) :
    dBmodel (flatMetric h₀) q d a b = 0 := by
  have hfun : (fun q' : E4 => koszulChr (flatMetric h₀) q' a b) = fun _ => (0 : E4) := by
    funext q'
    exact koszulChr_flatMetric h₀ h0 q' a b
  rw [dBmodel, hfun]
  simp

/-- **The model flat metric is flat**: the model curvature `modelCurv` vanishes
identically. -/
theorem flat_sec (h₀ : ℝ) (h0 : h₀ ≠ 0) (q u v w : E4) :
    modelCurv (flatMetric h₀) q u v w = 0 := by
  rw [modelCurv, dBmodel_flatMetric h₀ h0, dBmodel_flatMetric h₀ h0,
    koszulChr_flatMetric h₀ h0, koszulChr_flatMetric h₀ h0]
  simp

end

end Work.Curvature
