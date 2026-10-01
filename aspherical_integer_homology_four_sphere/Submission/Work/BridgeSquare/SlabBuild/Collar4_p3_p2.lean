import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Collar4_p1
import Submission.Work.BridgeSquare.SlabBuild.Collar4_p2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.BridgeSquare.SlabBuild

open Convexity
open Work.Subdivision
open Work.MbarHomology
open Work.BridgeSquare.WallCollar

noncomputable section

-- The `ℤ`-action on the chain modules is reached through `ZSMul.toSMul`; making that instance the
-- preferred one lets `map_smul`/`smul_smul`/`smul_zero` fire (the device of `PlaneAff.lean`).
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

theorem tS4_120 : (fun k => tauV4 120 k + lamV4 120) = ![slabPt (-3/8) (-3/8) (1), slabPt (-1/2) (-3/8) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_121 : (fun k => tauV4 121 k + lamV4 121) = ![slabPt (-5/8) (-3/8) (1), slabPt (-1/2) (-3/8) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_122 : (fun k => tauV4 122 k + lamV4 122) = ![slabPt (-3/8) (-3/8) (1), slabPt (-3/8) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_123 : (fun k => tauV4 123 k + lamV4 123) = ![slabPt (-3/8) (-5/8) (1), slabPt (-3/8) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_124 : (fun k => tauV4 124 k + lamV4 124) = ![slabPt (-5/8) (-5/8) (1), slabPt (-5/8) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_125 : (fun k => tauV4 125 k + lamV4 125) = ![slabPt (-5/8) (-3/8) (1), slabPt (-5/8) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_126 : (fun k => tauV4 126 k + lamV4 126) = ![slabPt (-5/8) (-5/8) (1), slabPt (-1/2) (-5/8) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_127 : (fun k => tauV4 127 k + lamV4 127) = ![slabPt (-3/8) (-5/8) (1), slabPt (-1/2) (-5/8) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem brC4'_0 (i : Fin 3) : B4 (aC4' (0, i)) = vface (k := 1) i (fun k => colTri4 0 k + colLam4 0) := by
  rw [cS4_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_1 (i : Fin 3) : B4 (aC4' (1, i)) = vface (k := 1) i (fun k => colTri4 1 k + colLam4 1) := by
  rw [cS4_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_2 (i : Fin 3) : B4 (aC4' (2, i)) = vface (k := 1) i (fun k => colTri4 2 k + colLam4 2) := by
  rw [cS4_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_3 (i : Fin 3) : B4 (aC4' (3, i)) = vface (k := 1) i (fun k => colTri4 3 k + colLam4 3) := by
  rw [cS4_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_4 (i : Fin 3) : B4 (aC4' (4, i)) = vface (k := 1) i (fun k => colTri4 4 k + colLam4 4) := by
  rw [cS4_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_5 (i : Fin 3) : B4 (aC4' (5, i)) = vface (k := 1) i (fun k => colTri4 5 k + colLam4 5) := by
  rw [cS4_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_6 (i : Fin 3) : B4 (aC4' (6, i)) = vface (k := 1) i (fun k => colTri4 6 k + colLam4 6) := by
  rw [cS4_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_7 (i : Fin 3) : B4 (aC4' (7, i)) = vface (k := 1) i (fun k => colTri4 7 k + colLam4 7) := by
  rw [cS4_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_8 (i : Fin 3) : B4 (aC4' (8, i)) = vface (k := 1) i (fun k => colTri4 8 k + colLam4 8) := by
  rw [cS4_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_9 (i : Fin 3) : B4 (aC4' (9, i)) = vface (k := 1) i (fun k => colTri4 9 k + colLam4 9) := by
  rw [cS4_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_10 (i : Fin 3) : B4 (aC4' (10, i)) = vface (k := 1) i (fun k => colTri4 10 k + colLam4 10) := by
  rw [cS4_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_11 (i : Fin 3) : B4 (aC4' (11, i)) = vface (k := 1) i (fun k => colTri4 11 k + colLam4 11) := by
  rw [cS4_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_12 (i : Fin 3) : B4 (aC4' (12, i)) = vface (k := 1) i (fun k => colTri4 12 k + colLam4 12) := by
  rw [cS4_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_13 (i : Fin 3) : B4 (aC4' (13, i)) = vface (k := 1) i (fun k => colTri4 13 k + colLam4 13) := by
  rw [cS4_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_14 (i : Fin 3) : B4 (aC4' (14, i)) = vface (k := 1) i (fun k => colTri4 14 k + colLam4 14) := by
  rw [cS4_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_15 (i : Fin 3) : B4 (aC4' (15, i)) = vface (k := 1) i (fun k => colTri4 15 k + colLam4 15) := by
  rw [cS4_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_16 (i : Fin 3) : B4 (aC4' (16, i)) = vface (k := 1) i (fun k => colTri4 16 k + colLam4 16) := by
  rw [cS4_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_17 (i : Fin 3) : B4 (aC4' (17, i)) = vface (k := 1) i (fun k => colTri4 17 k + colLam4 17) := by
  rw [cS4_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_18 (i : Fin 3) : B4 (aC4' (18, i)) = vface (k := 1) i (fun k => colTri4 18 k + colLam4 18) := by
  rw [cS4_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_19 (i : Fin 3) : B4 (aC4' (19, i)) = vface (k := 1) i (fun k => colTri4 19 k + colLam4 19) := by
  rw [cS4_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_20 (i : Fin 3) : B4 (aC4' (20, i)) = vface (k := 1) i (fun k => colTri4 20 k + colLam4 20) := by
  rw [cS4_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_21 (i : Fin 3) : B4 (aC4' (21, i)) = vface (k := 1) i (fun k => colTri4 21 k + colLam4 21) := by
  rw [cS4_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_22 (i : Fin 3) : B4 (aC4' (22, i)) = vface (k := 1) i (fun k => colTri4 22 k + colLam4 22) := by
  rw [cS4_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_23 (i : Fin 3) : B4 (aC4' (23, i)) = vface (k := 1) i (fun k => colTri4 23 k + colLam4 23) := by
  rw [cS4_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_24 (i : Fin 3) : B4 (aC4' (24, i)) = vface (k := 1) i (fun k => colTri4 24 k + colLam4 24) := by
  rw [cS4_24]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_25 (i : Fin 3) : B4 (aC4' (25, i)) = vface (k := 1) i (fun k => colTri4 25 k + colLam4 25) := by
  rw [cS4_25]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_26 (i : Fin 3) : B4 (aC4' (26, i)) = vface (k := 1) i (fun k => colTri4 26 k + colLam4 26) := by
  rw [cS4_26]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_27 (i : Fin 3) : B4 (aC4' (27, i)) = vface (k := 1) i (fun k => colTri4 27 k + colLam4 27) := by
  rw [cS4_27]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_28 (i : Fin 3) : B4 (aC4' (28, i)) = vface (k := 1) i (fun k => colTri4 28 k + colLam4 28) := by
  rw [cS4_28]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_29 (i : Fin 3) : B4 (aC4' (29, i)) = vface (k := 1) i (fun k => colTri4 29 k + colLam4 29) := by
  rw [cS4_29]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_30 (i : Fin 3) : B4 (aC4' (30, i)) = vface (k := 1) i (fun k => colTri4 30 k + colLam4 30) := by
  rw [cS4_30]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_31 (i : Fin 3) : B4 (aC4' (31, i)) = vface (k := 1) i (fun k => colTri4 31 k + colLam4 31) := by
  rw [cS4_31]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_32 (i : Fin 3) : B4 (aC4' (32, i)) = vface (k := 1) i (fun k => colTri4 32 k + colLam4 32) := by
  rw [cS4_32]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_33 (i : Fin 3) : B4 (aC4' (33, i)) = vface (k := 1) i (fun k => colTri4 33 k + colLam4 33) := by
  rw [cS4_33]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_34 (i : Fin 3) : B4 (aC4' (34, i)) = vface (k := 1) i (fun k => colTri4 34 k + colLam4 34) := by
  rw [cS4_34]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_35 (i : Fin 3) : B4 (aC4' (35, i)) = vface (k := 1) i (fun k => colTri4 35 k + colLam4 35) := by
  rw [cS4_35]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_36 (i : Fin 3) : B4 (aC4' (36, i)) = vface (k := 1) i (fun k => colTri4 36 k + colLam4 36) := by
  rw [cS4_36]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_37 (i : Fin 3) : B4 (aC4' (37, i)) = vface (k := 1) i (fun k => colTri4 37 k + colLam4 37) := by
  rw [cS4_37]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_38 (i : Fin 3) : B4 (aC4' (38, i)) = vface (k := 1) i (fun k => colTri4 38 k + colLam4 38) := by
  rw [cS4_38]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_39 (i : Fin 3) : B4 (aC4' (39, i)) = vface (k := 1) i (fun k => colTri4 39 k + colLam4 39) := by
  rw [cS4_39]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_40 (i : Fin 3) : B4 (aC4' (40, i)) = vface (k := 1) i (fun k => colTri4 40 k + colLam4 40) := by
  rw [cS4_40]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_41 (i : Fin 3) : B4 (aC4' (41, i)) = vface (k := 1) i (fun k => colTri4 41 k + colLam4 41) := by
  rw [cS4_41]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_42 (i : Fin 3) : B4 (aC4' (42, i)) = vface (k := 1) i (fun k => colTri4 42 k + colLam4 42) := by
  rw [cS4_42]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_43 (i : Fin 3) : B4 (aC4' (43, i)) = vface (k := 1) i (fun k => colTri4 43 k + colLam4 43) := by
  rw [cS4_43]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_44 (i : Fin 3) : B4 (aC4' (44, i)) = vface (k := 1) i (fun k => colTri4 44 k + colLam4 44) := by
  rw [cS4_44]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_45 (i : Fin 3) : B4 (aC4' (45, i)) = vface (k := 1) i (fun k => colTri4 45 k + colLam4 45) := by
  rw [cS4_45]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_46 (i : Fin 3) : B4 (aC4' (46, i)) = vface (k := 1) i (fun k => colTri4 46 k + colLam4 46) := by
  rw [cS4_46]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_47 (i : Fin 3) : B4 (aC4' (47, i)) = vface (k := 1) i (fun k => colTri4 47 k + colLam4 47) := by
  rw [cS4_47]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_0 (i : Fin 3) : B4 (aW4 (0, i)) = vface (k := 1) i (fun k => tauV4 0 k + lamV4 0) := by
  rw [tS4_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_1 (i : Fin 3) : B4 (aW4 (1, i)) = vface (k := 1) i (fun k => tauV4 1 k + lamV4 1) := by
  rw [tS4_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_2 (i : Fin 3) : B4 (aW4 (2, i)) = vface (k := 1) i (fun k => tauV4 2 k + lamV4 2) := by
  rw [tS4_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_3 (i : Fin 3) : B4 (aW4 (3, i)) = vface (k := 1) i (fun k => tauV4 3 k + lamV4 3) := by
  rw [tS4_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_4 (i : Fin 3) : B4 (aW4 (4, i)) = vface (k := 1) i (fun k => tauV4 4 k + lamV4 4) := by
  rw [tS4_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_5 (i : Fin 3) : B4 (aW4 (5, i)) = vface (k := 1) i (fun k => tauV4 5 k + lamV4 5) := by
  rw [tS4_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_6 (i : Fin 3) : B4 (aW4 (6, i)) = vface (k := 1) i (fun k => tauV4 6 k + lamV4 6) := by
  rw [tS4_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_7 (i : Fin 3) : B4 (aW4 (7, i)) = vface (k := 1) i (fun k => tauV4 7 k + lamV4 7) := by
  rw [tS4_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_8 (i : Fin 3) : B4 (aW4 (8, i)) = vface (k := 1) i (fun k => tauV4 8 k + lamV4 8) := by
  rw [tS4_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_9 (i : Fin 3) : B4 (aW4 (9, i)) = vface (k := 1) i (fun k => tauV4 9 k + lamV4 9) := by
  rw [tS4_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_10 (i : Fin 3) : B4 (aW4 (10, i)) = vface (k := 1) i (fun k => tauV4 10 k + lamV4 10) := by
  rw [tS4_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_11 (i : Fin 3) : B4 (aW4 (11, i)) = vface (k := 1) i (fun k => tauV4 11 k + lamV4 11) := by
  rw [tS4_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_12 (i : Fin 3) : B4 (aW4 (12, i)) = vface (k := 1) i (fun k => tauV4 12 k + lamV4 12) := by
  rw [tS4_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_13 (i : Fin 3) : B4 (aW4 (13, i)) = vface (k := 1) i (fun k => tauV4 13 k + lamV4 13) := by
  rw [tS4_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_14 (i : Fin 3) : B4 (aW4 (14, i)) = vface (k := 1) i (fun k => tauV4 14 k + lamV4 14) := by
  rw [tS4_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_15 (i : Fin 3) : B4 (aW4 (15, i)) = vface (k := 1) i (fun k => tauV4 15 k + lamV4 15) := by
  rw [tS4_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_16 (i : Fin 3) : B4 (aW4 (16, i)) = vface (k := 1) i (fun k => tauV4 16 k + lamV4 16) := by
  rw [tS4_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_17 (i : Fin 3) : B4 (aW4 (17, i)) = vface (k := 1) i (fun k => tauV4 17 k + lamV4 17) := by
  rw [tS4_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_18 (i : Fin 3) : B4 (aW4 (18, i)) = vface (k := 1) i (fun k => tauV4 18 k + lamV4 18) := by
  rw [tS4_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_19 (i : Fin 3) : B4 (aW4 (19, i)) = vface (k := 1) i (fun k => tauV4 19 k + lamV4 19) := by
  rw [tS4_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_20 (i : Fin 3) : B4 (aW4 (20, i)) = vface (k := 1) i (fun k => tauV4 20 k + lamV4 20) := by
  rw [tS4_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_21 (i : Fin 3) : B4 (aW4 (21, i)) = vface (k := 1) i (fun k => tauV4 21 k + lamV4 21) := by
  rw [tS4_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_22 (i : Fin 3) : B4 (aW4 (22, i)) = vface (k := 1) i (fun k => tauV4 22 k + lamV4 22) := by
  rw [tS4_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_23 (i : Fin 3) : B4 (aW4 (23, i)) = vface (k := 1) i (fun k => tauV4 23 k + lamV4 23) := by
  rw [tS4_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_24 (i : Fin 3) : B4 (aW4 (24, i)) = vface (k := 1) i (fun k => tauV4 24 k + lamV4 24) := by
  rw [tS4_24]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_25 (i : Fin 3) : B4 (aW4 (25, i)) = vface (k := 1) i (fun k => tauV4 25 k + lamV4 25) := by
  rw [tS4_25]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_26 (i : Fin 3) : B4 (aW4 (26, i)) = vface (k := 1) i (fun k => tauV4 26 k + lamV4 26) := by
  rw [tS4_26]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_27 (i : Fin 3) : B4 (aW4 (27, i)) = vface (k := 1) i (fun k => tauV4 27 k + lamV4 27) := by
  rw [tS4_27]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_28 (i : Fin 3) : B4 (aW4 (28, i)) = vface (k := 1) i (fun k => tauV4 28 k + lamV4 28) := by
  rw [tS4_28]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_29 (i : Fin 3) : B4 (aW4 (29, i)) = vface (k := 1) i (fun k => tauV4 29 k + lamV4 29) := by
  rw [tS4_29]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_30 (i : Fin 3) : B4 (aW4 (30, i)) = vface (k := 1) i (fun k => tauV4 30 k + lamV4 30) := by
  rw [tS4_30]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_31 (i : Fin 3) : B4 (aW4 (31, i)) = vface (k := 1) i (fun k => tauV4 31 k + lamV4 31) := by
  rw [tS4_31]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_32 (i : Fin 3) : B4 (aW4 (32, i)) = vface (k := 1) i (fun k => tauV4 32 k + lamV4 32) := by
  rw [tS4_32]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_33 (i : Fin 3) : B4 (aW4 (33, i)) = vface (k := 1) i (fun k => tauV4 33 k + lamV4 33) := by
  rw [tS4_33]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_34 (i : Fin 3) : B4 (aW4 (34, i)) = vface (k := 1) i (fun k => tauV4 34 k + lamV4 34) := by
  rw [tS4_34]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_35 (i : Fin 3) : B4 (aW4 (35, i)) = vface (k := 1) i (fun k => tauV4 35 k + lamV4 35) := by
  rw [tS4_35]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_36 (i : Fin 3) : B4 (aW4 (36, i)) = vface (k := 1) i (fun k => tauV4 36 k + lamV4 36) := by
  rw [tS4_36]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_37 (i : Fin 3) : B4 (aW4 (37, i)) = vface (k := 1) i (fun k => tauV4 37 k + lamV4 37) := by
  rw [tS4_37]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_38 (i : Fin 3) : B4 (aW4 (38, i)) = vface (k := 1) i (fun k => tauV4 38 k + lamV4 38) := by
  rw [tS4_38]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_39 (i : Fin 3) : B4 (aW4 (39, i)) = vface (k := 1) i (fun k => tauV4 39 k + lamV4 39) := by
  rw [tS4_39]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_40 (i : Fin 3) : B4 (aW4 (40, i)) = vface (k := 1) i (fun k => tauV4 40 k + lamV4 40) := by
  rw [tS4_40]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_41 (i : Fin 3) : B4 (aW4 (41, i)) = vface (k := 1) i (fun k => tauV4 41 k + lamV4 41) := by
  rw [tS4_41]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_42 (i : Fin 3) : B4 (aW4 (42, i)) = vface (k := 1) i (fun k => tauV4 42 k + lamV4 42) := by
  rw [tS4_42]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_43 (i : Fin 3) : B4 (aW4 (43, i)) = vface (k := 1) i (fun k => tauV4 43 k + lamV4 43) := by
  rw [tS4_43]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_44 (i : Fin 3) : B4 (aW4 (44, i)) = vface (k := 1) i (fun k => tauV4 44 k + lamV4 44) := by
  rw [tS4_44]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_45 (i : Fin 3) : B4 (aW4 (45, i)) = vface (k := 1) i (fun k => tauV4 45 k + lamV4 45) := by
  rw [tS4_45]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_46 (i : Fin 3) : B4 (aW4 (46, i)) = vface (k := 1) i (fun k => tauV4 46 k + lamV4 46) := by
  rw [tS4_46]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_47 (i : Fin 3) : B4 (aW4 (47, i)) = vface (k := 1) i (fun k => tauV4 47 k + lamV4 47) := by
  rw [tS4_47]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_48 (i : Fin 3) : B4 (aW4 (48, i)) = vface (k := 1) i (fun k => tauV4 48 k + lamV4 48) := by
  rw [tS4_48]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_49 (i : Fin 3) : B4 (aW4 (49, i)) = vface (k := 1) i (fun k => tauV4 49 k + lamV4 49) := by
  rw [tS4_49]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_50 (i : Fin 3) : B4 (aW4 (50, i)) = vface (k := 1) i (fun k => tauV4 50 k + lamV4 50) := by
  rw [tS4_50]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_51 (i : Fin 3) : B4 (aW4 (51, i)) = vface (k := 1) i (fun k => tauV4 51 k + lamV4 51) := by
  rw [tS4_51]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_52 (i : Fin 3) : B4 (aW4 (52, i)) = vface (k := 1) i (fun k => tauV4 52 k + lamV4 52) := by
  rw [tS4_52]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_53 (i : Fin 3) : B4 (aW4 (53, i)) = vface (k := 1) i (fun k => tauV4 53 k + lamV4 53) := by
  rw [tS4_53]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_54 (i : Fin 3) : B4 (aW4 (54, i)) = vface (k := 1) i (fun k => tauV4 54 k + lamV4 54) := by
  rw [tS4_54]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_55 (i : Fin 3) : B4 (aW4 (55, i)) = vface (k := 1) i (fun k => tauV4 55 k + lamV4 55) := by
  rw [tS4_55]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_56 (i : Fin 3) : B4 (aW4 (56, i)) = vface (k := 1) i (fun k => tauV4 56 k + lamV4 56) := by
  rw [tS4_56]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_57 (i : Fin 3) : B4 (aW4 (57, i)) = vface (k := 1) i (fun k => tauV4 57 k + lamV4 57) := by
  rw [tS4_57]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_58 (i : Fin 3) : B4 (aW4 (58, i)) = vface (k := 1) i (fun k => tauV4 58 k + lamV4 58) := by
  rw [tS4_58]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_59 (i : Fin 3) : B4 (aW4 (59, i)) = vface (k := 1) i (fun k => tauV4 59 k + lamV4 59) := by
  rw [tS4_59]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_60 (i : Fin 3) : B4 (aW4 (60, i)) = vface (k := 1) i (fun k => tauV4 60 k + lamV4 60) := by
  rw [tS4_60]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_61 (i : Fin 3) : B4 (aW4 (61, i)) = vface (k := 1) i (fun k => tauV4 61 k + lamV4 61) := by
  rw [tS4_61]; fin_cases i <;> funext k <;> fin_cases k <;> rfl

end

end Work.BridgeSquare.SlabBuild

