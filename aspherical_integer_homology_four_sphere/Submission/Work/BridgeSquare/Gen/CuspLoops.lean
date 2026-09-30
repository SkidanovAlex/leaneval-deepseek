/-
# `BridgeSquare/Gen/CuspLoops.lean` — the fibre loops of the cusp cube complexes

**This file is generated** by `Submission/Work/BridgeSquare/scripts/gen_cusp_loops.py` from the
exact data in `rtdata/` (the cube development `Cusp/Data.lean`, the orbit tables
`MbarOrbits.lean`, and `rt_complex.py`'s polytopal complex of `M̄`).  Do not edit by hand.

For every cusp `v` the *fibre loops* are the two coordinate loops of the cusp cube complex in
the `κ_{v,2}`, `κ_{v,3}` directions, and the *plane cycle* is the `κ_{v,2} ∧ κ_{v,3}` fundamental
2-cycle.  All of them are **boundaries** of `Gen.mbarCx` in degrees 1 and 2:

  `mbarBd 1 * fibreWit v = fibreLoop v`,   `mbarBd 2 * planeWit v = planeCycle v`,

with the witnesses below (all verified by `decide`).  This is the cellular half of
`Work.BridgeSquare.SubtorusNull` (`NOTES_SESSION3.md`).
-/
import Mathlib
import Submission.Work.HomologyIso.Gen.Mbar
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

namespace Work.BridgeSquare.Gen

open Work.Certificates
open Work.HomologyIso.Gen (mbarDim mbarBd)

/-! ## The loops -/

/-- **The ten fibre loops** (columns `(v, j)`, `v = 0..4`, `j = 0, 1`). -/
def fibreLoop : SOp (168) 10 :=
  SOp.ofList [
    [(23, 1), (146, 1)],
    [(47, -1), (62, 1)],
    [(8, -1), (29, 1)],
    [(20, 1), (149, 1)],
    [(65, 1), (158, 1)],
    [(77, -1), (89, 1)],
    [(101, -1), (113, 1)],
    [(119, 1), (164, 1)],
    [(4, 1), (7, -1), (25, -1), (28, 1)],
    [(36, -1), (37, 1), (51, 1), (52, -1)],
  ]

/-- The null-homology of `fibreLoop`. -/
def fibreWit : SOp (192) 10 :=
  SOp.ofList [
    [(0, 1), (1, -1), (2, 1), (3, -1), (8, -1), (9, 1), (36, 1), (37, -1), (56, 1), (68, -1), (72, 1), (78, -1), (103, 1), (136, 1), (137, -1), (142, -1), (143, 1), (148, 1), (149, -1), (184, 1)],
    [(2, 1), (8, -1), (9, 1), (12, -1), (13, 2), (14, -1), (15, 1), (16, 1), (19, -1), (21, -1), (22, -1), (24, -1), (30, 1), (33, 1), (36, 1), (37, -1), (38, 1), (39, -1), (42, -1), (43, 1), (44, -1), (45, 1), (49, -1), (61, 1), (63, 1), (75, -1), (87, 1), (88, 1), (110, -1), (112, 1), (115, 1), (117, -1), (120, -1), (121, 1)],
    [(5, -1), (11, 1), (17, 1), (24, -1), (25, 1), (30, 1), (31, -1), (36, 1), (37, -1), (38, 1), (39, -1), (42, -1), (43, 1), (44, -1), (45, 1), (97, -1), (104, 1), (108, 1), (109, -1)],
    [(0, -1), (1, 1), (2, -1), (3, 1), (4, 1), (5, -1), (6, 1), (8, 1), (97, -1), (98, 1), (99, -1), (100, 1), (101, 1), (137, 1), (139, 1), (185, 1)],
    [(3, -1), (9, 1), (19, 1), (21, 1), (117, 1), (136, 1), (142, -1), (148, 1), (150, 1), (188, 1)],
    [(2, 1), (8, -1), (9, 1), (12, -1), (13, 1), (14, -1), (24, -1), (30, 1), (31, -1), (36, 1), (38, 1), (42, -1), (43, 1), (44, -1), (45, 1), (49, -1), (61, 1), (63, 1), (75, -1), (76, -1), (87, 1), (88, 1), (94, -1), (118, 1), (120, -1), (122, -1), (124, 1)],
    [(0, 1), (1, -1), (2, 1), (3, -1), (4, -1), (24, -1), (25, 1), (36, 1), (37, -1), (72, 1), (73, -1), (78, -1), (79, 1), (99, 1), (100, -1), (129, -1), (133, 1)],
    [(78, 1), (80, 1), (135, 1), (161, 1), (163, 1), (190, 1)],
    [(1, -1), (3, -1), (7, 1), (9, 1), (52, 1), (99, 1), (106, -1)],
    [(41, -1), (108, -1), (113, 1)],
  ]

/-- `∂ fibreWit = fibreLoop`. -/
theorem fibreLoop_bd : ((mbarBd 1).mul fibreWit).eqb fibreLoop = true := by decide

/-- **The five plane 2-cycles** (column `v`). -/
def planeCycle : SOp (192) 5 :=
  SOp.ofList [
    [(16, 1), (22, -1), (152, 1), (158, -1)],
    [(5, 1), (11, -1), (141, 1), (147, -1)],
    [(88, 1), (94, -1), (176, 1), (182, -1)],
    [(77, 1), (83, -1), (165, 1), (171, -1)],
    [(24, -1), (25, 1), (26, -1), (27, 1), (30, 1), (31, -1), (32, 1), (33, -1), (36, 1), (37, -1), (38, 1), (39, -1), (42, -1), (43, 1), (44, -1), (45, 1)],
  ]

/-- The null-homology of `planeCycle`. -/
def planeWit : SOp (72) 5 :=
  SOp.ofList [
    [(2, 1), (3, -1), (6, -1), (7, 1), (10, 1), (11, -1), (14, -1), (15, 1), (21, 1), (26, 1), (27, -1), (40, -1), (41, 1), (44, 1), (45, -1), (48, -1), (49, 1), (52, 1), (53, -1), (60, 1), (66, 1), (67, -1)],
    [(8, 1), (9, -1), (10, 1), (11, -1), (12, -1), (13, 1), (14, -1), (15, 1), (17, 1), (24, -1), (25, 1), (40, -1), (41, 1), (42, -1), (43, 1), (44, 1), (45, -1), (46, 1), (47, -1), (56, 1), (64, -1), (65, 1)],
    [(1, 1), (3, 1), (5, -1), (7, -1), (9, 1), (11, 1), (13, -1), (15, -1), (23, 1), (38, 1), (39, -1), (40, 1), (42, 1), (44, -1), (46, -1), (48, 1), (50, 1), (52, -1), (54, -1), (62, 1), (70, 1), (71, -1)],
    [(0, 1), (1, -1), (2, 1), (3, -1), (8, 1), (9, -1), (10, 1), (11, -1), (19, 1), (36, -1), (37, 1), (44, 1), (45, -1), (46, 1), (47, -1), (52, 1), (53, -1), (54, 1), (55, -1), (58, 1), (68, -1), (69, 1)],
    [(18, 1), (19, -1), (20, -1), (21, 1), (28, 1), (29, -1), (30, -1), (31, 1)],
  ]

/-- `∂ planeWit = planeCycle`. -/
theorem planeCycle_bd : ((mbarBd 2).mul planeWit).eqb planeCycle = true := by decide
