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

theorem cS1_16 : (fun k => colTri1 16 k + colLam1 16) = ![slabPt (-1/4) (1/4) (1), slabPt (1/4) (1/4) (1), slabPt (0) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_17 : (fun k => colTri1 17 k + colLam1 17) = ![slabPt (1/4) (-1/2) (1), slabPt (1/4) (-1/4) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS1_18 : (fun k => colTri1 18 k + colLam1 18) = ![slabPt (1/4) (-1/2) (1), slabPt (1/4) (-3/4) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS1_19 : (fun k => colTri1 19 k + colLam1 19) = ![slabPt (1/4) (-1/4) (1), slabPt (1/4) (0) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS1_20 : (fun k => colTri1 20 k + colLam1 20) = ![slabPt (1/4) (0) (1), slabPt (1) (0) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_21 : (fun k => colTri1 21 k + colLam1 21) = ![slabPt (0) (1/4) (1), slabPt (0) (1) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_22 : (fun k => colTri1 22 k + colLam1 22) = ![slabPt (1) (0) (0), slabPt (1) (1) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1) (0) + slabPt (1) (0) (0) = slabPt (1) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_23 : (fun k => colTri1 23 k + colLam1 23) = ![slabPt (0) (1) (0), slabPt (1) (1) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1) (0) (0) + slabPt (0) (1) (0) = slabPt (1) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS1_0 : (fun k => tauV1 0 k + lamV1 0) = ![slabPt (-1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_1 : (fun k => tauV1 1 k + lamV1 1) = ![slabPt (1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_2 : (fun k => tauV1 2 k + lamV1 2) = ![slabPt (-1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_3 : (fun k => tauV1 3 k + lamV1 3) = ![slabPt (1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_4 : (fun k => tauV1 4 k + lamV1 4) = ![slabPt (1/4) (-1/4) (1), slabPt (1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_5 : (fun k => tauV1 5 k + lamV1 5) = ![slabPt (1/4) (1/4) (1), slabPt (1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_6 : (fun k => tauV1 6 k + lamV1 6) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_7 : (fun k => tauV1 7 k + lamV1 7) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_8 : (fun k => tauV1 8 k + lamV1 8) = ![slabPt (1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_9 : (fun k => tauV1 9 k + lamV1 9) = ![slabPt (-1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_10 : (fun k => tauV1 10 k + lamV1 10) = ![slabPt (1/4) (-3/4) (1), slabPt (0) (-3/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_11 : (fun k => tauV1 11 k + lamV1 11) = ![slabPt (-1/4) (-3/4) (1), slabPt (0) (-3/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_12 : (fun k => tauV1 12 k + lamV1 12) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_13 : (fun k => tauV1 13 k + lamV1 13) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_14 : (fun k => tauV1 14 k + lamV1 14) = ![slabPt (1/4) (-3/4) (1), slabPt (1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_15 : (fun k => tauV1 15 k + lamV1 15) = ![slabPt (1/4) (-1/4) (1), slabPt (1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_16 : (fun k => tauV1 16 k + lamV1 16) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/2) (1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_17 : (fun k => tauV1 17 k + lamV1 17) = ![slabPt (-3/4) (1/4) (1), slabPt (-1/2) (1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_18 : (fun k => tauV1 18 k + lamV1 18) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_19 : (fun k => tauV1 19 k + lamV1 19) = ![slabPt (-3/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_20 : (fun k => tauV1 20 k + lamV1 20) = ![slabPt (-3/4) (-1/4) (1), slabPt (-3/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_21 : (fun k => tauV1 21 k + lamV1 21) = ![slabPt (-3/4) (1/4) (1), slabPt (-3/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_22 : (fun k => tauV1 22 k + lamV1 22) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_23 : (fun k => tauV1 23 k + lamV1 23) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS1_24 : (fun k => tauV1 24 k + lamV1 24) = ![slabPt (-3/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_25 : (fun k => tauV1 25 k + lamV1 25) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_26 : (fun k => tauV1 26 k + lamV1 26) = ![slabPt (-3/4) (-3/4) (1), slabPt (-1/2) (-3/4) (1), slabPt (-1/2) (-1/2) (1)] := by
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

