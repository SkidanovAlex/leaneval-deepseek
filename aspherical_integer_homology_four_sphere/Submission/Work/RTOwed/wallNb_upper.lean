import Mathlib
import Submission.Work.RTOwed.cuspChartWalls
import Submission.Work.RTOwed.cuspDev

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- Consistency of the generated wall tables: the cube reached across the upper (`side = 1`) face
of the cube `a` in direction `j` is the cube of residue class `cubeCorner a + e_j`, and its lattice
vector is the difference of the corners shifted by the face offset.  Both are finite table
identities, discharged by kernel evaluation. -/
theorem wallNb_upper (a : Fin 48) (j : Fin 3) :
    Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp a)
        (fun l => Work.Cusp.cubeCorner a l + (if l = j then 1 else 0)) = Work.RTOwed.wallNb a j 1 ∧
    (∀ i : Fin 3, Work.RTOwed.wallLam a j 1 i
        = Work.Cusp.cubeCorner a i - Work.Cusp.cubeCorner (Work.RTOwed.wallNb a j 1) i
          + (if i = j then 1 else 0)) := by
  revert a j
  decide

end Work.RTOwed
