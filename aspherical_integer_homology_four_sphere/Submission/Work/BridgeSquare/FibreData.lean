/-
# `BridgeSquare/FibreData.lean` — the fibre loops, the cusp cubes, and the per-edge tables

**This file is generated** by `Submission/Work/BridgeSquare/scripts/gen_fibre_data.py` from the
exact Ratcliffe--Tschantz data (`Cusp/Data.lean`, `RTOwed/cuspDev.lean`, `MbarOrbits.lean` and
`rtdata/rt_complex.py`).  Do not edit by hand.  See `NOTES_SESSION3.md` for the mathematics.

Contents.

* `cubeIdeV` — the ideal vertex of each cube of the cusp development (0-based);
* `cubeWa` — the ideal vertex `w` with `kleinPt a (cubeCorner a) = (3/5) p_v + (2/5) p_w`;
* `cubeBitF` — the `ZMod 2` copy coordinate of each cube (`= if cubeCopy a then 0 else 1`);
* `dirKappa` — the cube-coordinate axis of `κ_{v,i}`;
* `fibreLoopVec`, `fibreWitVec`, `planeCycleVec`, `planeWitVec` — the loops as explicit vectors
  of `C_1`, `C_2`, `C_3` of `Gen.mbarCx` (positional indexing);
* the per-unit-edge tables `edgeCube`, `edgeFace`, `edgeW0Face`, `edgeW1Face`, `edgeCell`,
  `edgeSign`.

All certificates are `decide`/`norm_num` on the generated data (no `native_decide`).
-/
import Mathlib
import Submission.Work.BridgeSquare.Gen.CuspLoops
import Submission.Work.BridgeSquare.CuspSection
import Submission.Work.Cusp.Data
import Submission.Work.MbarHomology.Data.MbarOrbits

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Work.BridgeSquare

open Work.HomologyIso.Gen (mbarDim mbarBd)

noncomputable section

/-- The ideal vertex of the cube `a` of the cusp development (`cubeVertex` is `1`-based). -/
def cubeIdeV : Fin 48 → Fin 24 := fun a => ⟨Work.Cusp.cubeVertex a - 1, by
  have h : Work.Cusp.cubeVertex a ≤ 24 := by fin_cases a <;> decide
  omega⟩

/-- **The ideal vertex of the *lower corner* of the cube `a`**: `kleinPt a (cubeCorner a)` is the
point of the edge `[p_v, p_w]` of the 24-cell with `p_v·y = p_w·y = 4/5`, i.e.
`(3/5) p_v + (2/5) p_w`. -/
def cubeWa : Fin 48 → Fin 24 :=
  ![15, 3, 1, 13, 15, 2, 10, 7, 15, 5, 4, 14, 15, 8, 12, 11, 1, 21, 19, 16, 18, 21, 2, 3, 4, 8,
    15, 7, 11, 9, 10, 13, 22, 20, 19, 22, 17, 18, 16, 23, 20, 23, 5, 6, 14, 0, 12, 17]

/-- The `ZMod 2` copy coordinate of the cube `a`: the first component of `cuspPtX`. -/
def cubeBitF : Fin 48 → ZMod 2 := fun a => if Work.Cusp.cubeCopy a then 0 else 1

/-- The cube-coordinate axis of `κ_{v,i}` (`i = 0,1,2` for `κ_{v,1}, κ_{v,2}, κ_{v,3}`). -/
def dirKappa : Fin 5 → Fin 3 → Fin 3 :=
  ![![1, 2, 0], ![0, 2, 1], ![2, 1, 0], ![1, 2, 0], ![2, 1, 0]]

/-- The cube-coordinate axis of the `j`-th fibre loop of cusp `v` (`j = 0` is `κ_{v,2}`,
`j = 1` is `κ_{v,3}`). -/
def fibreDir (v : Fin 5) : Fin 2 → Fin 3 := fun j => dirKappa v (if j = 0 then 1 else 2)

/-- The length of the `j`-th fibre loop of cusp `v`. -/
def fibreLen (v : Fin 5) (j : Fin 2) : ℕ := Work.Cusp.latMod v (fibreDir v j)


/-- **The ten fibre-loop columns** of `C_1 (Gen.mbarCx)`: `(v, j)` with `j = 0` the `κ_{v,2}` loop and `j = 1` the `κ_{v,3}` loop (positional indexing of `mbarDim 1`). -/
def fibreLoopVec : Fin 5 → Fin 2 → (Fin 168 → ℤ) := fun v j i =>
  match (v : ℕ), (j : ℕ) with
  | 0, 0 => if i = 23 then (1 : ℤ) else (if i = 146 then (1 : ℤ) else (0))
  | 0, 1 => if i = 47 then (-1 : ℤ) else (if i = 62 then (1 : ℤ) else (0))
  | 1, 0 => if i = 8 then (-1 : ℤ) else (if i = 29 then (1 : ℤ) else (0))
  | 1, 1 => if i = 20 then (1 : ℤ) else (if i = 149 then (1 : ℤ) else (0))
  | 2, 0 => if i = 65 then (1 : ℤ) else (if i = 158 then (1 : ℤ) else (0))
  | 2, 1 => if i = 77 then (-1 : ℤ) else (if i = 89 then (1 : ℤ) else (0))
  | 3, 0 => if i = 101 then (-1 : ℤ) else (if i = 113 then (1 : ℤ) else (0))
  | 3, 1 => if i = 119 then (1 : ℤ) else (if i = 164 then (1 : ℤ) else (0))
  | 4, 0 => if i = 4 then (1 : ℤ) else (if i = 7 then (-1 : ℤ) else (if i = 25 then (-1 : ℤ) else (if i = 28 then (1 : ℤ) else (0))))
  | 4, 1 => if i = 36 then (-1 : ℤ) else (if i = 37 then (1 : ℤ) else (if i = 51 then (1 : ℤ) else (if i = 52 then (-1 : ℤ) else (0))))
  | _, _ => 0

/-- **The null-homologies**: `∂ (fibreWitVec v j) = fibreLoopVec v j`. -/
def fibreWitVec : Fin 5 → Fin 2 → (Fin 192 → ℤ) := fun v j i =>
  match (v : ℕ), (j : ℕ) with
  | 0, 0 => if i = 0 then (1 : ℤ) else (if i = 1 then (-1 : ℤ) else (if i = 2 then (1 : ℤ) else (if i = 3 then (-1 : ℤ) else (if i = 8 then (-1 : ℤ) else (if i = 9 then (1 : ℤ) else (if i = 36 then (1 : ℤ) else (if i = 37 then (-1 : ℤ) else (if i = 56 then (1 : ℤ) else (if i = 68 then (-1 : ℤ) else (if i = 72 then (1 : ℤ) else (if i = 78 then (-1 : ℤ) else (if i = 103 then (1 : ℤ) else (if i = 136 then (1 : ℤ) else (if i = 137 then (-1 : ℤ) else (if i = 142 then (-1 : ℤ) else (if i = 143 then (1 : ℤ) else (if i = 148 then (1 : ℤ) else (if i = 149 then (-1 : ℤ) else (if i = 184 then (1 : ℤ) else (0))))))))))))))))))))
  | 0, 1 => if i = 2 then (1 : ℤ) else (if i = 8 then (-1 : ℤ) else (if i = 9 then (1 : ℤ) else (if i = 12 then (-1 : ℤ) else (if i = 13 then (2 : ℤ) else (if i = 14 then (-1 : ℤ) else (if i = 15 then (1 : ℤ) else (if i = 16 then (1 : ℤ) else (if i = 19 then (-1 : ℤ) else (if i = 21 then (-1 : ℤ) else (if i = 22 then (-1 : ℤ) else (if i = 24 then (-1 : ℤ) else (if i = 30 then (1 : ℤ) else (if i = 33 then (1 : ℤ) else (if i = 36 then (1 : ℤ) else (if i = 37 then (-1 : ℤ) else (if i = 38 then (1 : ℤ) else (if i = 39 then (-1 : ℤ) else (if i = 42 then (-1 : ℤ) else (if i = 43 then (1 : ℤ) else (if i = 44 then (-1 : ℤ) else (if i = 45 then (1 : ℤ) else (if i = 49 then (-1 : ℤ) else (if i = 61 then (1 : ℤ) else (if i = 63 then (1 : ℤ) else (if i = 75 then (-1 : ℤ) else (if i = 87 then (1 : ℤ) else (if i = 88 then (1 : ℤ) else (if i = 110 then (-1 : ℤ) else (if i = 112 then (1 : ℤ) else (if i = 115 then (1 : ℤ) else (if i = 117 then (-1 : ℤ) else (if i = 120 then (-1 : ℤ) else (if i = 121 then (1 : ℤ) else (0))))))))))))))))))))))))))))))))))
  | 1, 0 => if i = 5 then (-1 : ℤ) else (if i = 11 then (1 : ℤ) else (if i = 17 then (1 : ℤ) else (if i = 24 then (-1 : ℤ) else (if i = 25 then (1 : ℤ) else (if i = 30 then (1 : ℤ) else (if i = 31 then (-1 : ℤ) else (if i = 36 then (1 : ℤ) else (if i = 37 then (-1 : ℤ) else (if i = 38 then (1 : ℤ) else (if i = 39 then (-1 : ℤ) else (if i = 42 then (-1 : ℤ) else (if i = 43 then (1 : ℤ) else (if i = 44 then (-1 : ℤ) else (if i = 45 then (1 : ℤ) else (if i = 97 then (-1 : ℤ) else (if i = 104 then (1 : ℤ) else (if i = 108 then (1 : ℤ) else (if i = 109 then (-1 : ℤ) else (0)))))))))))))))))))
  | 1, 1 => if i = 0 then (-1 : ℤ) else (if i = 1 then (1 : ℤ) else (if i = 2 then (-1 : ℤ) else (if i = 3 then (1 : ℤ) else (if i = 4 then (1 : ℤ) else (if i = 5 then (-1 : ℤ) else (if i = 6 then (1 : ℤ) else (if i = 8 then (1 : ℤ) else (if i = 97 then (-1 : ℤ) else (if i = 98 then (1 : ℤ) else (if i = 99 then (-1 : ℤ) else (if i = 100 then (1 : ℤ) else (if i = 101 then (1 : ℤ) else (if i = 137 then (1 : ℤ) else (if i = 139 then (1 : ℤ) else (if i = 185 then (1 : ℤ) else (0))))))))))))))))
  | 2, 0 => if i = 3 then (-1 : ℤ) else (if i = 9 then (1 : ℤ) else (if i = 19 then (1 : ℤ) else (if i = 21 then (1 : ℤ) else (if i = 117 then (1 : ℤ) else (if i = 136 then (1 : ℤ) else (if i = 142 then (-1 : ℤ) else (if i = 148 then (1 : ℤ) else (if i = 150 then (1 : ℤ) else (if i = 188 then (1 : ℤ) else (0))))))))))
  | 2, 1 => if i = 2 then (1 : ℤ) else (if i = 8 then (-1 : ℤ) else (if i = 9 then (1 : ℤ) else (if i = 12 then (-1 : ℤ) else (if i = 13 then (1 : ℤ) else (if i = 14 then (-1 : ℤ) else (if i = 24 then (-1 : ℤ) else (if i = 30 then (1 : ℤ) else (if i = 31 then (-1 : ℤ) else (if i = 36 then (1 : ℤ) else (if i = 38 then (1 : ℤ) else (if i = 42 then (-1 : ℤ) else (if i = 43 then (1 : ℤ) else (if i = 44 then (-1 : ℤ) else (if i = 45 then (1 : ℤ) else (if i = 49 then (-1 : ℤ) else (if i = 61 then (1 : ℤ) else (if i = 63 then (1 : ℤ) else (if i = 75 then (-1 : ℤ) else (if i = 76 then (-1 : ℤ) else (if i = 87 then (1 : ℤ) else (if i = 88 then (1 : ℤ) else (if i = 94 then (-1 : ℤ) else (if i = 118 then (1 : ℤ) else (if i = 120 then (-1 : ℤ) else (if i = 122 then (-1 : ℤ) else (if i = 124 then (1 : ℤ) else (0)))))))))))))))))))))))))))
  | 3, 0 => if i = 0 then (1 : ℤ) else (if i = 1 then (-1 : ℤ) else (if i = 2 then (1 : ℤ) else (if i = 3 then (-1 : ℤ) else (if i = 4 then (-1 : ℤ) else (if i = 24 then (-1 : ℤ) else (if i = 25 then (1 : ℤ) else (if i = 36 then (1 : ℤ) else (if i = 37 then (-1 : ℤ) else (if i = 72 then (1 : ℤ) else (if i = 73 then (-1 : ℤ) else (if i = 78 then (-1 : ℤ) else (if i = 79 then (1 : ℤ) else (if i = 99 then (1 : ℤ) else (if i = 100 then (-1 : ℤ) else (if i = 129 then (-1 : ℤ) else (if i = 133 then (1 : ℤ) else (0)))))))))))))))))
  | 3, 1 => if i = 78 then (1 : ℤ) else (if i = 80 then (1 : ℤ) else (if i = 135 then (1 : ℤ) else (if i = 161 then (1 : ℤ) else (if i = 163 then (1 : ℤ) else (if i = 190 then (1 : ℤ) else (0))))))
  | 4, 0 => if i = 1 then (-1 : ℤ) else (if i = 3 then (-1 : ℤ) else (if i = 7 then (1 : ℤ) else (if i = 9 then (1 : ℤ) else (if i = 52 then (1 : ℤ) else (if i = 99 then (1 : ℤ) else (if i = 106 then (-1 : ℤ) else (0)))))))
  | 4, 1 => if i = 41 then (-1 : ℤ) else (if i = 108 then (-1 : ℤ) else (if i = 113 then (1 : ℤ) else (0)))
  | _, _ => 0

/-- **The five plane `κ_{v,2} ∧ κ_{v,3}` cycles** of `C_2 (Gen.mbarCx)` (the `v`-th column; `j` is ignored). -/
def planeCycleVec : Fin 5 → Fin 2 → (Fin 192 → ℤ) := fun v j i =>
  match (v : ℕ), (j : ℕ) with
  | 0, 0 => if i = 16 then (1 : ℤ) else (if i = 22 then (-1 : ℤ) else (if i = 152 then (1 : ℤ) else (if i = 158 then (-1 : ℤ) else (0))))
  | 0, 1 => if i = 16 then (1 : ℤ) else (if i = 22 then (-1 : ℤ) else (if i = 152 then (1 : ℤ) else (if i = 158 then (-1 : ℤ) else (0))))
  | 1, 0 => if i = 5 then (1 : ℤ) else (if i = 11 then (-1 : ℤ) else (if i = 141 then (1 : ℤ) else (if i = 147 then (-1 : ℤ) else (0))))
  | 1, 1 => if i = 5 then (1 : ℤ) else (if i = 11 then (-1 : ℤ) else (if i = 141 then (1 : ℤ) else (if i = 147 then (-1 : ℤ) else (0))))
  | 2, 0 => if i = 88 then (1 : ℤ) else (if i = 94 then (-1 : ℤ) else (if i = 176 then (1 : ℤ) else (if i = 182 then (-1 : ℤ) else (0))))
  | 2, 1 => if i = 88 then (1 : ℤ) else (if i = 94 then (-1 : ℤ) else (if i = 176 then (1 : ℤ) else (if i = 182 then (-1 : ℤ) else (0))))
  | 3, 0 => if i = 77 then (1 : ℤ) else (if i = 83 then (-1 : ℤ) else (if i = 165 then (1 : ℤ) else (if i = 171 then (-1 : ℤ) else (0))))
  | 3, 1 => if i = 77 then (1 : ℤ) else (if i = 83 then (-1 : ℤ) else (if i = 165 then (1 : ℤ) else (if i = 171 then (-1 : ℤ) else (0))))
  | 4, 0 => if i = 24 then (-1 : ℤ) else (if i = 25 then (1 : ℤ) else (if i = 26 then (-1 : ℤ) else (if i = 27 then (1 : ℤ) else (if i = 30 then (1 : ℤ) else (if i = 31 then (-1 : ℤ) else (if i = 32 then (1 : ℤ) else (if i = 33 then (-1 : ℤ) else (if i = 36 then (1 : ℤ) else (if i = 37 then (-1 : ℤ) else (if i = 38 then (1 : ℤ) else (if i = 39 then (-1 : ℤ) else (if i = 42 then (-1 : ℤ) else (if i = 43 then (1 : ℤ) else (if i = 44 then (-1 : ℤ) else (if i = 45 then (1 : ℤ) else (0))))))))))))))))
  | 4, 1 => if i = 24 then (-1 : ℤ) else (if i = 25 then (1 : ℤ) else (if i = 26 then (-1 : ℤ) else (if i = 27 then (1 : ℤ) else (if i = 30 then (1 : ℤ) else (if i = 31 then (-1 : ℤ) else (if i = 32 then (1 : ℤ) else (if i = 33 then (-1 : ℤ) else (if i = 36 then (1 : ℤ) else (if i = 37 then (-1 : ℤ) else (if i = 38 then (1 : ℤ) else (if i = 39 then (-1 : ℤ) else (if i = 42 then (-1 : ℤ) else (if i = 43 then (1 : ℤ) else (if i = 44 then (-1 : ℤ) else (if i = 45 then (1 : ℤ) else (0))))))))))))))))
  | _, _ => 0

/-- **The null-homologies**: `∂ (planeWitVec v) = planeCycleVec v`. -/
def planeWitVec : Fin 5 → Fin 2 → (Fin 72 → ℤ) := fun v j i =>
  match (v : ℕ), (j : ℕ) with
  | 0, 0 => if i = 2 then (1 : ℤ) else (if i = 3 then (-1 : ℤ) else (if i = 6 then (-1 : ℤ) else (if i = 7 then (1 : ℤ) else (if i = 10 then (1 : ℤ) else (if i = 11 then (-1 : ℤ) else (if i = 14 then (-1 : ℤ) else (if i = 15 then (1 : ℤ) else (if i = 21 then (1 : ℤ) else (if i = 26 then (1 : ℤ) else (if i = 27 then (-1 : ℤ) else (if i = 40 then (-1 : ℤ) else (if i = 41 then (1 : ℤ) else (if i = 44 then (1 : ℤ) else (if i = 45 then (-1 : ℤ) else (if i = 48 then (-1 : ℤ) else (if i = 49 then (1 : ℤ) else (if i = 52 then (1 : ℤ) else (if i = 53 then (-1 : ℤ) else (if i = 60 then (1 : ℤ) else (if i = 66 then (1 : ℤ) else (if i = 67 then (-1 : ℤ) else (0))))))))))))))))))))))
  | 0, 1 => if i = 2 then (1 : ℤ) else (if i = 3 then (-1 : ℤ) else (if i = 6 then (-1 : ℤ) else (if i = 7 then (1 : ℤ) else (if i = 10 then (1 : ℤ) else (if i = 11 then (-1 : ℤ) else (if i = 14 then (-1 : ℤ) else (if i = 15 then (1 : ℤ) else (if i = 21 then (1 : ℤ) else (if i = 26 then (1 : ℤ) else (if i = 27 then (-1 : ℤ) else (if i = 40 then (-1 : ℤ) else (if i = 41 then (1 : ℤ) else (if i = 44 then (1 : ℤ) else (if i = 45 then (-1 : ℤ) else (if i = 48 then (-1 : ℤ) else (if i = 49 then (1 : ℤ) else (if i = 52 then (1 : ℤ) else (if i = 53 then (-1 : ℤ) else (if i = 60 then (1 : ℤ) else (if i = 66 then (1 : ℤ) else (if i = 67 then (-1 : ℤ) else (0))))))))))))))))))))))
  | 1, 0 => if i = 8 then (1 : ℤ) else (if i = 9 then (-1 : ℤ) else (if i = 10 then (1 : ℤ) else (if i = 11 then (-1 : ℤ) else (if i = 12 then (-1 : ℤ) else (if i = 13 then (1 : ℤ) else (if i = 14 then (-1 : ℤ) else (if i = 15 then (1 : ℤ) else (if i = 17 then (1 : ℤ) else (if i = 24 then (-1 : ℤ) else (if i = 25 then (1 : ℤ) else (if i = 40 then (-1 : ℤ) else (if i = 41 then (1 : ℤ) else (if i = 42 then (-1 : ℤ) else (if i = 43 then (1 : ℤ) else (if i = 44 then (1 : ℤ) else (if i = 45 then (-1 : ℤ) else (if i = 46 then (1 : ℤ) else (if i = 47 then (-1 : ℤ) else (if i = 56 then (1 : ℤ) else (if i = 64 then (-1 : ℤ) else (if i = 65 then (1 : ℤ) else (0))))))))))))))))))))))
  | 1, 1 => if i = 8 then (1 : ℤ) else (if i = 9 then (-1 : ℤ) else (if i = 10 then (1 : ℤ) else (if i = 11 then (-1 : ℤ) else (if i = 12 then (-1 : ℤ) else (if i = 13 then (1 : ℤ) else (if i = 14 then (-1 : ℤ) else (if i = 15 then (1 : ℤ) else (if i = 17 then (1 : ℤ) else (if i = 24 then (-1 : ℤ) else (if i = 25 then (1 : ℤ) else (if i = 40 then (-1 : ℤ) else (if i = 41 then (1 : ℤ) else (if i = 42 then (-1 : ℤ) else (if i = 43 then (1 : ℤ) else (if i = 44 then (1 : ℤ) else (if i = 45 then (-1 : ℤ) else (if i = 46 then (1 : ℤ) else (if i = 47 then (-1 : ℤ) else (if i = 56 then (1 : ℤ) else (if i = 64 then (-1 : ℤ) else (if i = 65 then (1 : ℤ) else (0))))))))))))))))))))))
  | 2, 0 => if i = 1 then (1 : ℤ) else (if i = 3 then (1 : ℤ) else (if i = 5 then (-1 : ℤ) else (if i = 7 then (-1 : ℤ) else (if i = 9 then (1 : ℤ) else (if i = 11 then (1 : ℤ) else (if i = 13 then (-1 : ℤ) else (if i = 15 then (-1 : ℤ) else (if i = 23 then (1 : ℤ) else (if i = 38 then (1 : ℤ) else (if i = 39 then (-1 : ℤ) else (if i = 40 then (1 : ℤ) else (if i = 42 then (1 : ℤ) else (if i = 44 then (-1 : ℤ) else (if i = 46 then (-1 : ℤ) else (if i = 48 then (1 : ℤ) else (if i = 50 then (1 : ℤ) else (if i = 52 then (-1 : ℤ) else (if i = 54 then (-1 : ℤ) else (if i = 62 then (1 : ℤ) else (if i = 70 then (1 : ℤ) else (if i = 71 then (-1 : ℤ) else (0))))))))))))))))))))))
  | 2, 1 => if i = 1 then (1 : ℤ) else (if i = 3 then (1 : ℤ) else (if i = 5 then (-1 : ℤ) else (if i = 7 then (-1 : ℤ) else (if i = 9 then (1 : ℤ) else (if i = 11 then (1 : ℤ) else (if i = 13 then (-1 : ℤ) else (if i = 15 then (-1 : ℤ) else (if i = 23 then (1 : ℤ) else (if i = 38 then (1 : ℤ) else (if i = 39 then (-1 : ℤ) else (if i = 40 then (1 : ℤ) else (if i = 42 then (1 : ℤ) else (if i = 44 then (-1 : ℤ) else (if i = 46 then (-1 : ℤ) else (if i = 48 then (1 : ℤ) else (if i = 50 then (1 : ℤ) else (if i = 52 then (-1 : ℤ) else (if i = 54 then (-1 : ℤ) else (if i = 62 then (1 : ℤ) else (if i = 70 then (1 : ℤ) else (if i = 71 then (-1 : ℤ) else (0))))))))))))))))))))))
  | 3, 0 => if i = 0 then (1 : ℤ) else (if i = 1 then (-1 : ℤ) else (if i = 2 then (1 : ℤ) else (if i = 3 then (-1 : ℤ) else (if i = 8 then (1 : ℤ) else (if i = 9 then (-1 : ℤ) else (if i = 10 then (1 : ℤ) else (if i = 11 then (-1 : ℤ) else (if i = 19 then (1 : ℤ) else (if i = 36 then (-1 : ℤ) else (if i = 37 then (1 : ℤ) else (if i = 44 then (1 : ℤ) else (if i = 45 then (-1 : ℤ) else (if i = 46 then (1 : ℤ) else (if i = 47 then (-1 : ℤ) else (if i = 52 then (1 : ℤ) else (if i = 53 then (-1 : ℤ) else (if i = 54 then (1 : ℤ) else (if i = 55 then (-1 : ℤ) else (if i = 58 then (1 : ℤ) else (if i = 68 then (-1 : ℤ) else (if i = 69 then (1 : ℤ) else (0))))))))))))))))))))))
  | 3, 1 => if i = 0 then (1 : ℤ) else (if i = 1 then (-1 : ℤ) else (if i = 2 then (1 : ℤ) else (if i = 3 then (-1 : ℤ) else (if i = 8 then (1 : ℤ) else (if i = 9 then (-1 : ℤ) else (if i = 10 then (1 : ℤ) else (if i = 11 then (-1 : ℤ) else (if i = 19 then (1 : ℤ) else (if i = 36 then (-1 : ℤ) else (if i = 37 then (1 : ℤ) else (if i = 44 then (1 : ℤ) else (if i = 45 then (-1 : ℤ) else (if i = 46 then (1 : ℤ) else (if i = 47 then (-1 : ℤ) else (if i = 52 then (1 : ℤ) else (if i = 53 then (-1 : ℤ) else (if i = 54 then (1 : ℤ) else (if i = 55 then (-1 : ℤ) else (if i = 58 then (1 : ℤ) else (if i = 68 then (-1 : ℤ) else (if i = 69 then (1 : ℤ) else (0))))))))))))))))))))))
  | 4, 0 => if i = 18 then (1 : ℤ) else (if i = 19 then (-1 : ℤ) else (if i = 20 then (-1 : ℤ) else (if i = 21 then (1 : ℤ) else (if i = 28 then (1 : ℤ) else (if i = 29 then (-1 : ℤ) else (if i = 30 then (-1 : ℤ) else (if i = 31 then (1 : ℤ) else (0))))))))
  | 4, 1 => if i = 18 then (1 : ℤ) else (if i = 19 then (-1 : ℤ) else (if i = 20 then (-1 : ℤ) else (if i = 21 then (1 : ℤ) else (if i = 28 then (1 : ℤ) else (if i = 29 then (-1 : ℤ) else (if i = 30 then (-1 : ℤ) else (if i = 31 then (1 : ℤ) else (0))))))))
  | _, _ => 0

/-- The cube carrying the `k`-th unit edge of the `j`-th fibre loop of cusp `v`. -/
def edgeCube : Fin 5 → Fin 2 → Fin 4 → Fin 48 := fun v j k =>
  match (v : ℕ), (j : ℕ), (k : ℕ) with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 2
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 0
  | 0, 1, 1 => 1
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 1, 0, 0 => 4
  | 1, 0, 1 => 6
  | 1, 0, 2 => 0
  | 1, 0, 3 => 0
  | 1, 1, 0 => 4
  | 1, 1, 1 => 5
  | 1, 1, 2 => 0
  | 1, 1, 3 => 0
  | 2, 0, 0 => 8
  | 2, 0, 1 => 10
  | 2, 0, 2 => 0
  | 2, 0, 3 => 0
  | 2, 1, 0 => 8
  | 2, 1, 1 => 9
  | 2, 1, 2 => 0
  | 2, 1, 3 => 0
  | 3, 0, 0 => 12
  | 3, 0, 1 => 14
  | 3, 0, 2 => 0
  | 3, 0, 3 => 0
  | 3, 1, 0 => 12
  | 3, 1, 1 => 13
  | 3, 1, 2 => 0
  | 3, 1, 3 => 0
  | 4, 0, 0 => 16
  | 4, 0, 1 => 20
  | 4, 0, 2 => 27
  | 4, 0, 3 => 18
  | 4, 1, 0 => 16
  | 4, 1, 1 => 21
  | 4, 1, 2 => 25
  | 4, 1, 3 => 17
  | _, _, _ => 0

/-- The ridge (a `0`-face `('C', v, r)` of `Q̄`) of the `k`-th unit edge. -/
def edgeFace : Fin 5 → Fin 2 → Fin 4 → Fin 865 := fun v j k =>
  match (v : ℕ), (j : ℕ), (k : ℕ) with
  | 0, 0, 0 => 196
  | 0, 0, 1 => 296
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 332
  | 0, 1, 1 => 356
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 1, 0, 0 => 204
  | 1, 0, 1 => 268
  | 1, 0, 2 => 0
  | 1, 0, 3 => 0
  | 1, 1, 0 => 220
  | 1, 1, 1 => 320
  | 1, 1, 2 => 0
  | 1, 1, 3 => 0
  | 2, 0, 0 => 340
  | 2, 0, 1 => 416
  | 2, 0, 2 => 0
  | 2, 0, 3 => 0
  | 2, 1, 0 => 428
  | 2, 1, 1 => 460
  | 2, 1, 2 => 0
  | 2, 1, 3 => 0
  | 3, 0, 0 => 484
  | 3, 0, 1 => 516
  | 3, 0, 2 => 0
  | 3, 0, 3 => 0
  | 3, 1, 0 => 548
  | 3, 1, 1 => 576
  | 3, 1, 2 => 0
  | 3, 1, 3 => 0
  | 4, 0, 0 => 302
  | 4, 0, 1 => 238
  | 4, 0, 2 => 234
  | 4, 0, 3 => 298
  | 4, 1, 0 => 398
  | 4, 1, 1 => 399
  | 4, 1, 2 => 375
  | 4, 1, 3 => 374
  | _, _, _ => 0

/-- The `0`-face `('C', v, [v, w_0])` at the lower endpoint. -/
def edgeW0Face : Fin 5 → Fin 2 → Fin 4 → Fin 865 := fun v j k =>
  match (v : ℕ), (j : ℕ), (k : ℕ) with
  | 0, 0, 0 => 855
  | 0, 0, 1 => 612
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 855
  | 0, 1, 1 => 651
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 1, 0, 0 => 858
  | 1, 0, 1 => 783
  | 1, 0, 2 => 0
  | 1, 0, 3 => 0
  | 1, 1, 0 => 858
  | 1, 1, 1 => 636
  | 1, 1, 2 => 0
  | 1, 1, 3 => 0
  | 2, 0, 0 => 861
  | 2, 0, 1 => 678
  | 2, 0, 2 => 0
  | 2, 0, 3 => 0
  | 2, 1, 0 => 861
  | 2, 1, 1 => 696
  | 2, 1, 2 => 0
  | 2, 1, 3 => 0
  | 3, 0, 0 => 864
  | 3, 0, 1 => 822
  | 3, 0, 2 => 0
  | 3, 0, 3 => 0
  | 3, 1, 0 => 864
  | 3, 1, 1 => 753
  | 3, 1, 2 => 0
  | 3, 1, 3 => 0
  | 4, 0, 0 => 578
  | 4, 0, 1 => 674
  | 4, 0, 2 => 701
  | 4, 0, 3 => 635
  | 4, 1, 0 => 578
  | 4, 1, 1 => 617
  | 4, 1, 2 => 735
  | 4, 1, 3 => 749
  | _, _, _ => 0

/-- The `0`-face `('C', v, [v, w_1])` at the upper endpoint. -/
def edgeW1Face : Fin 5 → Fin 2 → Fin 4 → Fin 865 := fun v j k =>
  match (v : ℕ), (j : ℕ), (k : ℕ) with
  | 0, 0, 0 => 843
  | 0, 0, 1 => 591
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 795
  | 0, 1, 1 => 723
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 1, 0, 0 => 846
  | 1, 0, 1 => 798
  | 1, 0, 2 => 0
  | 1, 0, 3 => 0
  | 1, 1, 0 => 831
  | 1, 1, 1 => 594
  | 1, 1, 2 => 0
  | 1, 1, 3 => 0
  | 2, 0, 0 => 801
  | 2, 0, 1 => 597
  | 2, 0, 2 => 0
  | 2, 0, 3 => 0
  | 2, 1, 0 => 729
  | 2, 1, 1 => 834
  | 2, 1, 2 => 0
  | 2, 1, 3 => 0
  | 3, 0, 0 => 837
  | 3, 0, 1 => 852
  | 3, 0, 2 => 0
  | 3, 0, 3 => 0
  | 3, 1, 0 => 732
  | 3, 1, 1 => 600
  | 3, 1, 2 => 0
  | 3, 1, 3 => 0
  | 4, 0, 0 => 593
  | 4, 0, 1 => 662
  | 4, 0, 2 => 710
  | 4, 0, 3 => 623
  | 4, 1, 0 => 596
  | 4, 1, 1 => 579
  | 4, 1, 2 => 767
  | 4, 1, 3 => 734
  | _, _, _ => 0

/-- The cell (positional index of `C_1`) of the `k`-th unit edge. -/
def edgeCell : Fin 5 → Fin 2 → Fin 4 → Fin 168 := fun v j k =>
  match (v : ℕ), (j : ℕ), (k : ℕ) with
  | 0, 0, 0 => 146
  | 0, 0, 1 => 23
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 62
  | 0, 1, 1 => 47
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 1, 0, 0 => 29
  | 1, 0, 1 => 8
  | 1, 0, 2 => 0
  | 1, 0, 3 => 0
  | 1, 1, 0 => 149
  | 1, 1, 1 => 20
  | 1, 1, 2 => 0
  | 1, 1, 3 => 0
  | 2, 0, 0 => 158
  | 2, 0, 1 => 65
  | 2, 0, 2 => 0
  | 2, 0, 3 => 0
  | 2, 1, 0 => 89
  | 2, 1, 1 => 77
  | 2, 1, 2 => 0
  | 2, 1, 3 => 0
  | 3, 0, 0 => 113
  | 3, 0, 1 => 101
  | 3, 0, 2 => 0
  | 3, 0, 3 => 0
  | 3, 1, 0 => 164
  | 3, 1, 1 => 119
  | 3, 1, 2 => 0
  | 3, 1, 3 => 0
  | 4, 0, 0 => 4
  | 4, 0, 1 => 25
  | 4, 0, 2 => 28
  | 4, 0, 3 => 7
  | 4, 1, 0 => 37
  | 4, 1, 1 => 36
  | 4, 1, 2 => 51
  | 4, 1, 3 => 52
  | _, _, _ => 0

/-- The sign of the `k`-th unit edge in the fibre loop. -/
def edgeSign : Fin 5 → Fin 2 → Fin 4 → ℤ := fun v j k =>
  match (v : ℕ), (j : ℕ), (k : ℕ) with
  | 0, 0, 0 => 1
  | 0, 0, 1 => 1
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 1
  | 0, 1, 1 => -1
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 1, 0, 0 => 1
  | 1, 0, 1 => -1
  | 1, 0, 2 => 0
  | 1, 0, 3 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 0
  | 1, 1, 3 => 0
  | 2, 0, 0 => 1
  | 2, 0, 1 => 1
  | 2, 0, 2 => 0
  | 2, 0, 3 => 0
  | 2, 1, 0 => 1
  | 2, 1, 1 => -1
  | 2, 1, 2 => 0
  | 2, 1, 3 => 0
  | 3, 0, 0 => 1
  | 3, 0, 1 => -1
  | 3, 0, 2 => 0
  | 3, 0, 3 => 0
  | 3, 1, 0 => 1
  | 3, 1, 1 => 1
  | 3, 1, 2 => 0
  | 3, 1, 3 => 0
  | 4, 0, 0 => 1
  | 4, 0, 1 => -1
  | 4, 0, 2 => 1
  | 4, 0, 3 => -1
  | 4, 1, 0 => 1
  | 4, 1, 1 => -1
  | 4, 1, 2 => 1
  | 4, 1, 3 => -1
  | _, _, _ => 0


/- **The per-edge certificates** — the bridge between the cube development and the cell complex:
the `k`-th unit edge of the `j`-th fibre loop of cusp `v` is the cell of the node
`(cubeBitF a, 'C'(v,r))` of the polytopal complex `Gen.mbarCx`, and it occurs in the loop with
coefficient `edgeSign`. -/

/-- **The unit edges are the cells of the corresponding nodes.** -/
theorem edge_cell_eq (v : Fin 5) (j : Fin 2) (k : Fin 4) (hk : (k : ℕ) < fibreLen v j) :
    Work.MbarHomology.Mbar.moPos
        (Work.MbarHomology.Mbar.moCell
          (cubeBitF (edgeCube v j k)) (edgeFace v j k))
      = (edgeCell v j k : ℕ) := by
  fin_cases v <;> fin_cases j <;> fin_cases k <;>
    simp only [fibreLen, fibreDir, dirKappa, Work.Cusp.latMod] at hk <;>
    first | (exact absurd hk (by decide)) | decide

/-- Each unit edge does occur in the fibre loop, with coefficient `edgeSign`. -/
theorem fibreLoop_edge (v : Fin 5) (j : Fin 2) (k : Fin 4) (hk : (k : ℕ) < fibreLen v j) :
    fibreLoopVec v j (edgeCell v j k) = edgeSign v j k := by
  fin_cases v <;> fin_cases j <;> fin_cases k <;>
    simp only [fibreLen, fibreDir, dirKappa, Work.Cusp.latMod] at hk <;>
    first | (exact absurd hk (by decide)) | decide

end

end Work.BridgeSquare
