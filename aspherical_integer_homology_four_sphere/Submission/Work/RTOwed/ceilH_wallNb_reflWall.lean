import Mathlib
import Submission.Work.RTOwed.cuspChartWallReflect
import Submission.Work.RTOwed.cuspWallTableCerts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The ceiling of a cube across a wall (W-ceiling)

The ceiling `ceilH a x` of the cube `a` is the hemisphere of radius `3/2` centred at
`cubeCorner a + (1/2, 1/2, 1/2)`, i.e.
`ceilH a x = sqrt (9/4 - ∑ i, (x i - (cubeCorner a i + 1/2))^2)`.

This file proves that the ceiling is compatible with the wall identification of
`Submission/Work/RTOwed/cuspChartWallReflect.lean`: on the lower face `side = 0` of the wall
`{x m = cubeCorner a m}`, transporting the coordinate by the lattice vector `wallLam a m 0`
into the neighbouring cube `wallNb a m 0` is the same as reflecting the coordinate in the wall
plane, so the two ceilings agree:

  `ceilH (wallNb a m 0) (v - wallLam a m 0) = ceilH a (reflWall m (cubeCorner a m) v)`.

Both sides are hemispheres of the same radius, and the arithmetic identity of the centres is the
finite certificate (`cuspWallTableCerts`) relating `cubeCorner (wallNb a m 0)` and `cubeCorner a`
through `wallLam a m 0`:

* across the wall (`i = m`): `cubeCorner (wallNb a m 0) m + wallLam a m 0 m = cubeCorner a m - 1`;
* tangentially (`j ≠ m`):  `cubeCorner (wallNb a m 0) j + wallLam a m 0 j = cubeCorner a j`.

Hence the two centre-difference vectors are negatives of one another across the wall and equal
tangentially, so the sums of squares coincide.
-/

open scoped BigOperators

namespace Work.RTOwed

/-- **`ceilH` depends only on the squared centre differences.**  If the squared differences of
`x` from the centre of the cube `b` coincide coordinatewise with those of `y` from the centre of
the cube `c`, then the two ceilings agree. -/
lemma ceilH_eq_of_forall_sq (b c : Fin 48) (x y : CuspE3)
    (h : ∀ j : Fin 3, (x j - ((Work.Cusp.cubeCorner b j : ℝ) + 1/2))^2
      = (y j - ((Work.Cusp.cubeCorner c j : ℝ) + 1/2))^2) :
    ceilH b x = ceilH c y := by
  have hs : (∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner b j : ℝ) + 1/2))^2)
      = (∑ j : Fin 3, (y j - ((Work.Cusp.cubeCorner c j : ℝ) + 1/2))^2) :=
    Finset.sum_congr rfl (fun j _ => h j)
  simp only [ceilH, hs]

theorem ceilH_wallNb_reflWall (a : Fin 48) (m : Fin 3) (v : Work.RTOwed.CuspE3) :
    Work.RTOwed.ceilH (Work.RTOwed.wallNb a m 0) (v - Work.RTOwed.wallLamV a m 0)
      = Work.RTOwed.ceilH a (Work.RTOwed.reflWall m (Work.Cusp.cubeCorner a m : ℝ) v) := by
  have hNorm := cuspWallTableCerts.2.2.1 a m 0
  have hTan := cuspWallTableCerts.2.2.2.1 a m 0
  simp only at hNorm
  refine ceilH_eq_of_forall_sq _ _ _ _ (fun j => ?_)
  by_cases hj : j = m
  · -- the normal direction across the wall
    subst hj
    have hv : (v - wallLamV a j 0) j = v j - wallLamV a j 0 j := by simp [wallLamV]
    have hr : reflWall j (Work.Cusp.cubeCorner a j : ℝ) v j
        = 2 * (Work.Cusp.cubeCorner a j : ℝ) - v j := by rw [reflWall_self]
    rw [hv, hr]
    have hrel : (Work.Cusp.cubeCorner (wallNb a j 0) j : ℝ) + wallLamV a j 0 j + 1
        = (Work.Cusp.cubeCorner a j : ℝ) := by simpa using hNorm
    have h1 : v j - wallLamV a j 0 j - ((Work.Cusp.cubeCorner (wallNb a j 0) j : ℝ) + 1/2)
        = -(2 * (Work.Cusp.cubeCorner a j : ℝ) - v j
            - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2)) := by
      linarith
    rw [h1]; ring
  · -- the tangential directions along the wall
    have hrel := hTan j hj
    have hv : (v - wallLamV a m 0) j = v j - wallLamV a m 0 j := by simp [wallLamV]
    have hr : reflWall m (Work.Cusp.cubeCorner a m : ℝ) v j = v j :=
      reflWall_of_ne hj _ _
    rw [hv, hr]
    have h1 : v j - wallLamV a m 0 j - ((Work.Cusp.cubeCorner (wallNb a m 0) j : ℝ) + 1/2)
        = v j - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2) := by linarith
    rw [h1]

end Work.RTOwed
