import Mathlib
import Submission.Work.RTOwed.cuspCert.tsetCoverData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 0
set_option maxRecDepth 4000000

namespace Work.RTOwed.cuspCert

/-! ### The four table facts of `covData`

The cover data of the truncation set are finite tables (`covB`, `covF`, `satOf`, `latOf`,
`covGam`), and the four identities of `covData` are equalities between values of these tables at
indices `(a, e, i)` of the finite types `Fin 48 × Fin 8 × Fin 3`.  Each is therefore a decidable
prop, verified here by kernel evaluation (`decide`) of the tables.

The only subtlety is the fourth identity: the sum `∑ i, ...` of `Gg`-elements forces the kernel to
normalise the product group `Gg = (Fin 4 → ZMod 2) × ZMod 2` for all `48 · 8` index pairs, which
exceeds the default recursion depth; hence the raised `maxRecDepth` below. -/

/-- The cusp of the neighbour cube is the cusp of the cube. -/
theorem covData_cusp (a : Fin 48) (e : Fin 8) :
    Work.Cusp.cubeCusp (covB a e) = Work.Cusp.cubeCusp a := by
  revert a e; decide +kernel

/-- The corner of the neighbour cube: the shift of the corner by the saturation pattern minus the
lattice offset. -/
theorem covData_corner (a : Fin 48) (e : Fin 8) (i : Fin 3) :
    Work.Cusp.cubeCorner (covB a e) i =
      Work.Cusp.cubeCorner a i + satOf e i - latOf a e i := by
  revert a e i; decide +kernel

/-- The copy bit of the neighbour cube: the copy bit of `a` flipped by `covF`. -/
theorem covData_bit (a : Fin 48) (e : Fin 8) :
    Work.RTOwed.cubeBit (covB a e) + covF a e = Work.RTOwed.cubeBit a := by
  revert a e; decide +kernel

/-- The gluing element `covGam a e` is the sum of the type generators of the walls of the
neighbour cube `covB a e` at the saturated coordinates. -/
theorem covData_gam (a : Fin 48) (e : Fin 8) :
    covGam a e =
      ∑ i : Fin 3, if satOf e i = 1 then
        Work.FoldInst.typeGen (Work.FoldInst.sideTypeIdx
          (Work.RTOwed.wallLo (covB a e) i)) else 0 := by
  revert a e; decide +kernel

theorem covData :
    (∀ (a : Fin 48) (e : Fin 8), Work.Cusp.cubeCusp (Work.RTOwed.cuspCert.covB a e) = Work.Cusp.cubeCusp a) ∧
    (∀ (a : Fin 48) (e : Fin 8) (i : Fin 3), Work.Cusp.cubeCorner (Work.RTOwed.cuspCert.covB a e) i =
      Work.Cusp.cubeCorner a i + Work.RTOwed.cuspCert.satOf e i - Work.RTOwed.cuspCert.latOf a e i) ∧
    (∀ (a : Fin 48) (e : Fin 8), Work.RTOwed.cubeBit (Work.RTOwed.cuspCert.covB a e) +
        Work.RTOwed.cuspCert.covF a e = Work.RTOwed.cubeBit a) ∧
    (∀ (a : Fin 48) (e : Fin 8), Work.RTOwed.cuspCert.covGam a e =
      ∑ i : Fin 3, if Work.RTOwed.cuspCert.satOf e i = 1 then
        Work.FoldInst.typeGen (Work.FoldInst.sideTypeIdx
          (Work.RTOwed.wallLo (Work.RTOwed.cuspCert.covB a e) i)) else 0) :=
  ⟨fun a e => covData_cusp a e, fun a e i => covData_corner a e i,
   fun a e => covData_bit a e, fun a e => covData_gam a e⟩

end Work.RTOwed.cuspCert
