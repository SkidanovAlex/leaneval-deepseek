import Mathlib
import Submission.Work.RTOwed.cuspChart
import Submission.Work.RTOwed.cuspCertWalls
import Submission.Work.RTOwed.cuspDev
import Submission.Work.RTOwed.cuspCert.mbarPt_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

/-- The wall table of the cusp cubes, together with its consistency certificates: all six are
finite checks on the tables `wallNb`, `wallLam`, `wallGamK`, `wallGamFlip` of
`cuspCertWalls.lean` against the fixed data (`wallLo`, `wallHi`, `cubeCorner`, `cubeCusp`,
`latMod`).  Each integer/bit statement is discharged by `decide` (kernel reduction, no extra
axioms); the two statements mentioning `ℝ` are reduced to their integer counterparts and then
cast, and the last one exhibits the lattice coefficient vector explicitly. -/
theorem cuspWallTableCerts :
    (∀ (a : Fin 48) (i : Fin 3) (side : Fin 2),
      (wallGamK a i side, wallGamFlip a i side)
        = Work.FoldInst.sideType (if side = 0 then wallLo a i else wallHi a i))
    ∧ (∀ (a : Fin 48) (i : Fin 3) (side : Fin 2),
      cubeBit (wallNb a i side) = cubeBit a + wallGamFlip a i side)
    ∧ (∀ (a : Fin 48) (i : Fin 3) (side : Fin 2),
      (Work.Cusp.cubeCorner (wallNb a i side) i : ℝ) + wallLamV a i side i
        + (if side = 0 then 1 else 0) = (Work.Cusp.cubeCorner a i : ℝ) + (if side = 0 then 0 else 1))
    ∧ (∀ (a : Fin 48) (i : Fin 3) (side : Fin 2) (j : Fin 3), j ≠ i →
      (Work.Cusp.cubeCorner (wallNb a i side) j : ℝ) + wallLamV a i side j
        = (Work.Cusp.cubeCorner a j : ℝ))
    ∧ (∀ (a : Fin 48) (i : Fin 3) (side : Fin 2) (j : Fin 3) (sj : Fin 2),
      Work.FoldInst.sideType
        (if j = i then (if sj = 0 then wallHi (wallNb a i side) j else wallLo (wallNb a i side) j)
         else (if sj = 0 then wallLo (wallNb a i side) j else wallHi (wallNb a i side) j))
      = Work.FoldInst.sideType (if sj = 0 then wallLo a j else wallHi a j))
    ∧ (∀ (a : Fin 48) (i : Fin 3) (side : Fin 2),
      ∃ k : Fin 3 → ℤ, wallLamV a i side = cuspCert.lamV (Work.Cusp.cubeCusp a) k)
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the group element of a wall is the type of its near side
    decide +kernel
  · -- the copy bit of the far cube
    decide +kernel
  · -- the normal coordinate across the wall
    intro a i side
    have h : Work.Cusp.cubeCorner (wallNb a i side) i + wallLam a i side i
        + (if side = 0 then (1 : ℤ) else 0)
        = Work.Cusp.cubeCorner a i + (if side = 0 then (0 : ℤ) else 1) := by
      revert a i side
      decide +kernel
    simp only [wallLamV, PiLp.toLp_apply]
    exact_mod_cast h
  · -- the tangential coordinates along the wall
    intro a i side j hj
    have h : ∀ (a : Fin 48) (i : Fin 3) (side : Fin 2) (j : Fin 3), j ≠ i →
        Work.Cusp.cubeCorner (wallNb a i side) j + wallLam a i side j
          = Work.Cusp.cubeCorner a j := by
      decide +kernel
    simp only [wallLamV, PiLp.toLp_apply]
    exact_mod_cast h a i side j hj
  · -- the wall types of the far cube agree with those of the near cube
    intro a i side j sj
    have h : Work.FoldInst.sideTypeIdx
          (if j = i then (if sj = 0 then wallHi (wallNb a i side) j else wallLo (wallNb a i side) j)
           else (if sj = 0 then wallLo (wallNb a i side) j else wallHi (wallNb a i side) j))
        = Work.FoldInst.sideTypeIdx (if sj = 0 then wallLo a j else wallHi a j) := by
      revert a i side j sj
      decide +kernel
    exact congrArg Work.FoldInst.typeGen h
  · -- the lattice vector of a wall lies in the cusp lattice
    intro a i side
    refine ⟨fun j => wallLam a i side j / (Work.Cusp.latMod (Work.Cusp.cubeCusp a) j : ℤ), ?_⟩
    apply PiLp.ext
    intro j
    simp only [wallLamV, cuspCert.lamV, cuspCert.lamK, PiLp.toLp_apply]
    have h : (Work.Cusp.latMod (Work.Cusp.cubeCusp a) j : ℤ) ∣ wallLam a i side j := by
      revert a i side j
      decide +kernel
    rw [Int.mul_ediv_cancel' h]

end Work.RTOwed
