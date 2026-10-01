import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Infra

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

theorem cS3_16 : (fun k => colTri3 16 k + colLam3 16) = ![slabPt (-1/4) (1/4) (1), slabPt (1/4) (1/4) (1), slabPt (0) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_17 : (fun k => colTri3 17 k + colLam3 17) = ![slabPt (1/4) (-1/2) (1), slabPt (1/4) (-1/4) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS3_18 : (fun k => colTri3 18 k + colLam3 18) = ![slabPt (1/4) (-1/2) (1), slabPt (1/4) (-3/4) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS3_19 : (fun k => colTri3 19 k + colLam3 19) = ![slabPt (1/4) (-1/4) (1), slabPt (1/4) (0) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS3_20 : (fun k => colTri3 20 k + colLam3 20) = ![slabPt (1/4) (0) (1), slabPt (1) (0) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_21 : (fun k => colTri3 21 k + colLam3 21) = ![slabPt (0) (1/4) (1), slabPt (0) (1) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_22 : (fun k => colTri3 22 k + colLam3 22) = ![slabPt (1) (0) (0), slabPt (1) (1) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1) (0) + slabPt (1) (0) (0) = slabPt (1) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_23 : (fun k => colTri3 23 k + colLam3 23) = ![slabPt (0) (1) (0), slabPt (1) (1) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1) (0) (0) + slabPt (0) (1) (0) = slabPt (1) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS3_0 : (fun k => tauV3 0 k + lamV3 0) = ![slabPt (-1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_1 : (fun k => tauV3 1 k + lamV3 1) = ![slabPt (1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_2 : (fun k => tauV3 2 k + lamV3 2) = ![slabPt (-1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_3 : (fun k => tauV3 3 k + lamV3 3) = ![slabPt (1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_4 : (fun k => tauV3 4 k + lamV3 4) = ![slabPt (1/4) (-1/4) (1), slabPt (1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_5 : (fun k => tauV3 5 k + lamV3 5) = ![slabPt (1/4) (1/4) (1), slabPt (1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_6 : (fun k => tauV3 6 k + lamV3 6) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_7 : (fun k => tauV3 7 k + lamV3 7) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_8 : (fun k => tauV3 8 k + lamV3 8) = ![slabPt (1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_9 : (fun k => tauV3 9 k + lamV3 9) = ![slabPt (-1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_10 : (fun k => tauV3 10 k + lamV3 10) = ![slabPt (1/4) (-3/4) (1), slabPt (0) (-3/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_11 : (fun k => tauV3 11 k + lamV3 11) = ![slabPt (-1/4) (-3/4) (1), slabPt (0) (-3/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_12 : (fun k => tauV3 12 k + lamV3 12) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_13 : (fun k => tauV3 13 k + lamV3 13) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_14 : (fun k => tauV3 14 k + lamV3 14) = ![slabPt (1/4) (-3/4) (1), slabPt (1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_15 : (fun k => tauV3 15 k + lamV3 15) = ![slabPt (1/4) (-1/4) (1), slabPt (1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_16 : (fun k => tauV3 16 k + lamV3 16) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/2) (1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_17 : (fun k => tauV3 17 k + lamV3 17) = ![slabPt (-3/4) (1/4) (1), slabPt (-1/2) (1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_18 : (fun k => tauV3 18 k + lamV3 18) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_19 : (fun k => tauV3 19 k + lamV3 19) = ![slabPt (-3/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_20 : (fun k => tauV3 20 k + lamV3 20) = ![slabPt (-3/4) (-1/4) (1), slabPt (-3/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_21 : (fun k => tauV3 21 k + lamV3 21) = ![slabPt (-3/4) (1/4) (1), slabPt (-3/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_22 : (fun k => tauV3 22 k + lamV3 22) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_23 : (fun k => tauV3 23 k + lamV3 23) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS3_24 : (fun k => tauV3 24 k + lamV3 24) = ![slabPt (-3/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_25 : (fun k => tauV3 25 k + lamV3 25) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_26 : (fun k => tauV3 26 k + lamV3 26) = ![slabPt (-3/4) (-3/4) (1), slabPt (-1/2) (-3/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num


end

end Work.BridgeSquare.SlabBuild

