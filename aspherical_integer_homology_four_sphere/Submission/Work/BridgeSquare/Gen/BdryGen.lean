/-
# `BridgeSquare/Gen/BdryGen.lean` — boundary-supported generators of `H_k(M̄)`

**This file is generated** by `Submission/Work/BridgeSquare/scripts/gen_bdry_gen.py` from
the exact Ratcliffe--Tschantz data in `rtdata/`; do not edit by hand, rerun the script.

For `k = 1, 2, 3`, the sparse operator `bdryGen k : SOp (mbarDim k) (mbarB k)` has as its
`j`-th column a cycle of `Gen.mbarCx` supported on the *truncation cells* (the cells lying
in one of the five cusp cube complexes), and `bdryWit k : SOp (mbarDim (k+1)) (mbarB k)`
satisfies

  `bdryGen k - mbarZ k = mbarBd (k-1) * bdryWit k`.

Consequently `[bdryGen k]` is a set of generators of `H_k(Gen.mbarCx)` in degrees `1, 2, 3`
(SDR identity: `bdryGen k = mbarZ k` up to a boundary, column by column), and each of its
columns is carried by the truncation cells, so its image under the comparison `PsiM` lies
in the truncation torus `Tset = range cuspMap` — which is what makes the surjectivity `(c)`
of `NOTES_LEAD_aspherical_bridge.md` provable.
-/
import Mathlib
import Submission.Work.HomologyIso.Gen.Mbar
import Submission.Work.MbarHomology.Mbar.AtlasCx
import Submission.Work.BridgeSquare.PsiM

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open CategoryTheory

namespace Work.BridgeSquare.Gen

open Work.Certificates
open Work.HomologyIso.Gen (mbarDim mbarB mbarZ mbarBd)

/-! ### degree 1 -/

/-- **The truncation-supported generators of `H_1(M̄)`**: the `j`-th column is a cycle
supported on the truncation cells and homologous to the `j`-th SDR generator. -/
def bdryGenone : SOp 168 5 :=
  SOp.ofList [
    [(14, -1), (56, -1)],
    [(83, -1), (98, -1)],
    [(14, -1)],
    [(4, -1), (12, -1), (18, 1), (21, 1), (22, -1), (25, 1), (27, -1), (37, 1), (42, 1), (45, -1), (46, 1), (159, -1)],
    [(98, 1)],
  ]

/-- **The witnesses**: `bdryGenone - mbarZ 1 = mbarBd 1 * bdryWitone`. -/
def bdryWitone : SOp 192 5 :=
  SOp.ofList [
    [(4, 1), (7, 1), (9, 1), (23, -1), (38, -1), (39, 1), (41, -1), (44, 1), (45, -1), (52, 1), (98, 1), (101, 1), (106, -1), (108, -1)],
    [(2, -1), (3, 1), (8, 1), (9, -1), (12, 1), (14, 1), (15, -1), (24, 1), (25, -1), (30, -1), (31, 2), (33, 1), (34, 1), (36, -2), (37, 2), (38, -2), (39, 2), (41, -1), (42, 2), (43, -2), (44, 2), (45, -2), (52, -1), (53, 1), (61, -1), (63, -1), (82, 1), (88, 1), (99, -1), (106, 1), (108, -1), (112, 1), (113, 1), (118, -1), (121, 1), (127, -1)],
    [(4, 1), (99, -1), (129, 1)],
    [(0, -2), (1, 2), (2, -1), (3, 1), (7, -1), (12, -1), (13, 1), (14, -1), (15, 1), (36, -1), (37, 1), (38, 1), (39, -1), (44, -1), (45, 1), (56, -1), (68, 1), (72, -1), (73, 1), (78, 1), (79, -1), (143, -1), (148, -1), (149, 1), (154, 1), (162, -1)],
    [(53, -1)],
  ]

/-- The columns of `bdryGenone` are cycles. -/
theorem bdryGenone_cycle :
    ((mbarBd 0).mul bdryGenone).eqb (SOp.zero 48 5) = true := by
  decide

/-- Each column is homologous to the corresponding SDR generator. -/
theorem bdryGenone_hom :
    ((bdryGenone).sub (mbarZ 1)).eqb ((mbarBd 1).mul bdryWitone) = true := by
  decide

/-- Every nonzero entry of a generator lies in a truncation cell. -/
theorem bdryGenone_supp (j : Fin 5) :
    ((bdryGenone).img j).all (fun p => isTruncCell 1 p.1) = true := by
  fin_cases j <;> decide

/-! ### degree 2 -/

/-- **The truncation-supported generators of `H_2(M̄)`**: the `j`-th column is a cycle
supported on the truncation cells and homologous to the `j`-th SDR generator. -/
def bdryGentwo : SOp 192 10 :=
  SOp.ofList [
    [(52, -1), (58, 1)],
    [(2, 1), (3, -1), (20, -1), (21, 1), (33, -1), (49, 1), (75, 1), (81, -1), (136, 1), (142, -1), (143, 1), (148, 1), (149, -1), (156, 1), (160, -1), (179, 1)],
    [(1, 1), (3, 1), (7, -1), (9, -1), (136, -1), (138, -1), (142, 1), (144, 1)],
    [(35, -1), (47, 1)],
    [(4, -1), (146, 1)],
    [(17, 1), (159, -1)],
    [(53, 1), (65, -1)],
    [(89, 1), (183, -1)],
    [(28, 1), (34, -1)],
    [(35, -1), (47, 1), (76, -1), (170, 1)],
  ]

/-- **The witnesses**: `bdryGentwo - mbarZ 2 = mbarBd 2 * bdryWittwo`. -/
def bdryWittwo : SOp 72 10 :=
  SOp.ofList [
    [],
    [(4, 1), (5, -1)],
    [],
    [(10, 1), (11, -1), (19, 1), (29, 1), (31, -1), (37, 1)],
    [(17, -1), (24, 1), (25, -1), (56, -1), (64, 1)],
    [(2, 1), (3, -1), (6, -1), (7, 1), (21, 1), (27, -1), (48, -1), (49, 1), (52, 1), (53, -1), (60, 1), (66, 1)],
    [(22, 1), (23, -1)],
    [(1, 1), (5, -1), (9, 1), (13, -1), (23, 1), (39, -1), (42, 1), (46, -1), (50, 1), (54, -1), (62, 1), (70, 1)],
    [],
    [(10, 1), (11, -1), (29, 1), (31, -1), (58, -1), (68, 1)],
  ]

/-- The columns of `bdryGentwo` are cycles. -/
theorem bdryGentwo_cycle :
    ((mbarBd 1).mul bdryGentwo).eqb (SOp.zero 168 10) = true := by
  decide

/-- Each column is homologous to the corresponding SDR generator. -/
theorem bdryGentwo_hom :
    ((bdryGentwo).sub (mbarZ 2)).eqb ((mbarBd 2).mul bdryWittwo) = true := by
  decide

/-- Every nonzero entry of a generator lies in a truncation cell. -/
theorem bdryGentwo_supp (j : Fin 10) :
    ((bdryGentwo).img j).all (fun p => isTruncCell 2 p.1) = true := by
  fin_cases j <;> decide

/-! ### degree 3 -/

/-- **The truncation-supported generators of `H_3(M̄)`**: the `j`-th column is a cycle
supported on the truncation cells and homologous to the `j`-th SDR generator. -/
def bdryGenthree : SOp 72 4 :=
  SOp.ofList [
    [(22, 1), (23, -1), (62, -1), (63, 1)],
    [(16, 1), (17, -1), (56, -1), (57, 1)],
    [(16, -1), (17, 1), (18, 1), (19, -1), (20, -1), (21, 1), (22, 1), (23, -1), (56, 1), (57, -1), (58, -1), (59, 1), (60, 1), (61, -1), (62, -1), (63, 1)],
    [(18, 1), (19, -1), (58, -1), (59, 1)],
  ]

/-- **The witnesses**: `bdryGenthree - mbarZ 3 = mbarBd 3 * bdryWitthree`. -/
def bdryWitthree : SOp 2 4 :=
  SOp.ofList [
    [],
    [],
    [(0, -1), (1, 1)],
    [],
  ]

/-- The columns of `bdryGenthree` are cycles. -/
theorem bdryGenthree_cycle :
    ((mbarBd 2).mul bdryGenthree).eqb (SOp.zero 192 4) = true := by
  decide

/-- Each column is homologous to the corresponding SDR generator. -/
theorem bdryGenthree_hom :
    ((bdryGenthree).sub (mbarZ 3)).eqb ((mbarBd 3).mul bdryWitthree) = true := by
  decide

/-- Every nonzero entry of a generator lies in a truncation cell. -/
theorem bdryGenthree_supp (j : Fin 4) :
    ((bdryGenthree).img j).all (fun p => isTruncCell 3 p.1) = true := by
  fin_cases j <;> decide

end Work.BridgeSquare.Gen
