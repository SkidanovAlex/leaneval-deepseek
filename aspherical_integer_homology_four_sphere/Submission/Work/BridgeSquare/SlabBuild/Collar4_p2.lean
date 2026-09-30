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

theorem tS4_0 : (fun k => tauV4 0 k + lamV4 0) = ![slabPt (1/8) (1/8) (1), slabPt (0) (1/8) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_1 : (fun k => tauV4 1 k + lamV4 1) = ![slabPt (-1/8) (1/8) (1), slabPt (0) (1/8) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_2 : (fun k => tauV4 2 k + lamV4 2) = ![slabPt (1/8) (1/8) (1), slabPt (1/8) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_3 : (fun k => tauV4 3 k + lamV4 3) = ![slabPt (1/8) (-1/8) (1), slabPt (1/8) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_4 : (fun k => tauV4 4 k + lamV4 4) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/8) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_5 : (fun k => tauV4 5 k + lamV4 5) = ![slabPt (-1/8) (1/8) (1), slabPt (-1/8) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_6 : (fun k => tauV4 6 k + lamV4 6) = ![slabPt (-1/8) (-1/8) (1), slabPt (0) (-1/8) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_7 : (fun k => tauV4 7 k + lamV4 7) = ![slabPt (1/8) (-1/8) (1), slabPt (0) (-1/8) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_8 : (fun k => tauV4 8 k + lamV4 8) = ![slabPt (1/8) (-7/8) (1), slabPt (0) (-7/8) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_9 : (fun k => tauV4 9 k + lamV4 9) = ![slabPt (-1/8) (-7/8) (1), slabPt (0) (-7/8) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_10 : (fun k => tauV4 10 k + lamV4 10) = ![slabPt (1/8) (-7/8) (1), slabPt (1/8) (-3/4) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_11 : (fun k => tauV4 11 k + lamV4 11) = ![slabPt (1/8) (-5/8) (1), slabPt (1/8) (-3/4) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_12 : (fun k => tauV4 12 k + lamV4 12) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/8) (-3/4) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_13 : (fun k => tauV4 13 k + lamV4 13) = ![slabPt (-1/8) (-7/8) (1), slabPt (-1/8) (-3/4) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_14 : (fun k => tauV4 14 k + lamV4 14) = ![slabPt (-1/8) (-5/8) (1), slabPt (0) (-5/8) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_15 : (fun k => tauV4 15 k + lamV4 15) = ![slabPt (1/8) (-5/8) (1), slabPt (0) (-5/8) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_16 : (fun k => tauV4 16 k + lamV4 16) = ![slabPt (-7/8) (1/8) (1), slabPt (-3/4) (1/8) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_17 : (fun k => tauV4 17 k + lamV4 17) = ![slabPt (-5/8) (1/8) (1), slabPt (-3/4) (1/8) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_18 : (fun k => tauV4 18 k + lamV4 18) = ![slabPt (-7/8) (1/8) (1), slabPt (-7/8) (0) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_19 : (fun k => tauV4 19 k + lamV4 19) = ![slabPt (-7/8) (-1/8) (1), slabPt (-7/8) (0) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_20 : (fun k => tauV4 20 k + lamV4 20) = ![slabPt (-5/8) (-1/8) (1), slabPt (-5/8) (0) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_21 : (fun k => tauV4 21 k + lamV4 21) = ![slabPt (-5/8) (1/8) (1), slabPt (-5/8) (0) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_22 : (fun k => tauV4 22 k + lamV4 22) = ![slabPt (-5/8) (-1/8) (1), slabPt (-3/4) (-1/8) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_23 : (fun k => tauV4 23 k + lamV4 23) = ![slabPt (-7/8) (-1/8) (1), slabPt (-3/4) (-1/8) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_24 : (fun k => tauV4 24 k + lamV4 24) = ![slabPt (-3/8) (1/8) (1), slabPt (-1/4) (1/8) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_25 : (fun k => tauV4 25 k + lamV4 25) = ![slabPt (-1/8) (1/8) (1), slabPt (-1/4) (1/8) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_26 : (fun k => tauV4 26 k + lamV4 26) = ![slabPt (-3/8) (1/8) (1), slabPt (-3/8) (0) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_27 : (fun k => tauV4 27 k + lamV4 27) = ![slabPt (-3/8) (-1/8) (1), slabPt (-3/8) (0) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_28 : (fun k => tauV4 28 k + lamV4 28) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/8) (0) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_29 : (fun k => tauV4 29 k + lamV4 29) = ![slabPt (-1/8) (1/8) (1), slabPt (-1/8) (0) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_30 : (fun k => tauV4 30 k + lamV4 30) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/4) (-1/8) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_31 : (fun k => tauV4 31 k + lamV4 31) = ![slabPt (-3/8) (-1/8) (1), slabPt (-1/4) (-1/8) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_32 : (fun k => tauV4 32 k + lamV4 32) = ![slabPt (1/8) (-3/8) (1), slabPt (0) (-3/8) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_33 : (fun k => tauV4 33 k + lamV4 33) = ![slabPt (-1/8) (-3/8) (1), slabPt (0) (-3/8) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_34 : (fun k => tauV4 34 k + lamV4 34) = ![slabPt (1/8) (-3/8) (1), slabPt (1/8) (-1/4) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_35 : (fun k => tauV4 35 k + lamV4 35) = ![slabPt (1/8) (-1/8) (1), slabPt (1/8) (-1/4) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_36 : (fun k => tauV4 36 k + lamV4 36) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/8) (-1/4) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_37 : (fun k => tauV4 37 k + lamV4 37) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/8) (-1/4) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_38 : (fun k => tauV4 38 k + lamV4 38) = ![slabPt (-1/8) (-1/8) (1), slabPt (0) (-1/8) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_39 : (fun k => tauV4 39 k + lamV4 39) = ![slabPt (1/8) (-1/8) (1), slabPt (0) (-1/8) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_40 : (fun k => tauV4 40 k + lamV4 40) = ![slabPt (-7/8) (-7/8) (1), slabPt (-3/4) (-7/8) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_41 : (fun k => tauV4 41 k + lamV4 41) = ![slabPt (-5/8) (-7/8) (1), slabPt (-3/4) (-7/8) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_42 : (fun k => tauV4 42 k + lamV4 42) = ![slabPt (-7/8) (-7/8) (1), slabPt (-7/8) (-3/4) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_43 : (fun k => tauV4 43 k + lamV4 43) = ![slabPt (-7/8) (-5/8) (1), slabPt (-7/8) (-3/4) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_44 : (fun k => tauV4 44 k + lamV4 44) = ![slabPt (-5/8) (-5/8) (1), slabPt (-5/8) (-3/4) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_45 : (fun k => tauV4 45 k + lamV4 45) = ![slabPt (-5/8) (-7/8) (1), slabPt (-5/8) (-3/4) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_46 : (fun k => tauV4 46 k + lamV4 46) = ![slabPt (-5/8) (-5/8) (1), slabPt (-3/4) (-5/8) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_47 : (fun k => tauV4 47 k + lamV4 47) = ![slabPt (-7/8) (-5/8) (1), slabPt (-3/4) (-5/8) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_48 : (fun k => tauV4 48 k + lamV4 48) = ![slabPt (-3/8) (-7/8) (1), slabPt (-1/4) (-7/8) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_49 : (fun k => tauV4 49 k + lamV4 49) = ![slabPt (-1/8) (-7/8) (1), slabPt (-1/4) (-7/8) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_50 : (fun k => tauV4 50 k + lamV4 50) = ![slabPt (-3/8) (-7/8) (1), slabPt (-3/8) (-3/4) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_51 : (fun k => tauV4 51 k + lamV4 51) = ![slabPt (-3/8) (-5/8) (1), slabPt (-3/8) (-3/4) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_52 : (fun k => tauV4 52 k + lamV4 52) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/8) (-3/4) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_53 : (fun k => tauV4 53 k + lamV4 53) = ![slabPt (-1/8) (-7/8) (1), slabPt (-1/8) (-3/4) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_54 : (fun k => tauV4 54 k + lamV4 54) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/4) (-5/8) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_55 : (fun k => tauV4 55 k + lamV4 55) = ![slabPt (-3/8) (-5/8) (1), slabPt (-1/4) (-5/8) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_56 : (fun k => tauV4 56 k + lamV4 56) = ![slabPt (1/8) (-3/8) (1), slabPt (0) (-3/8) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_57 : (fun k => tauV4 57 k + lamV4 57) = ![slabPt (-1/8) (-3/8) (1), slabPt (0) (-3/8) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_58 : (fun k => tauV4 58 k + lamV4 58) = ![slabPt (1/8) (-3/8) (1), slabPt (1/8) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_59 : (fun k => tauV4 59 k + lamV4 59) = ![slabPt (1/8) (-5/8) (1), slabPt (1/8) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_60 : (fun k => tauV4 60 k + lamV4 60) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/8) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_61 : (fun k => tauV4 61 k + lamV4 61) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/8) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_62 : (fun k => tauV4 62 k + lamV4 62) = ![slabPt (-1/8) (-5/8) (1), slabPt (0) (-5/8) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_63 : (fun k => tauV4 63 k + lamV4 63) = ![slabPt (1/8) (-5/8) (1), slabPt (0) (-5/8) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_64 : (fun k => tauV4 64 k + lamV4 64) = ![slabPt (-3/8) (1/8) (1), slabPt (-1/2) (1/8) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_65 : (fun k => tauV4 65 k + lamV4 65) = ![slabPt (-5/8) (1/8) (1), slabPt (-1/2) (1/8) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_66 : (fun k => tauV4 66 k + lamV4 66) = ![slabPt (-3/8) (1/8) (1), slabPt (-3/8) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_67 : (fun k => tauV4 67 k + lamV4 67) = ![slabPt (-3/8) (-1/8) (1), slabPt (-3/8) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_68 : (fun k => tauV4 68 k + lamV4 68) = ![slabPt (-5/8) (-1/8) (1), slabPt (-5/8) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_69 : (fun k => tauV4 69 k + lamV4 69) = ![slabPt (-5/8) (1/8) (1), slabPt (-5/8) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_70 : (fun k => tauV4 70 k + lamV4 70) = ![slabPt (-5/8) (-1/8) (1), slabPt (-1/2) (-1/8) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_71 : (fun k => tauV4 71 k + lamV4 71) = ![slabPt (-3/8) (-1/8) (1), slabPt (-1/2) (-1/8) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_72 : (fun k => tauV4 72 k + lamV4 72) = ![slabPt (-7/8) (-3/8) (1), slabPt (-3/4) (-3/8) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_73 : (fun k => tauV4 73 k + lamV4 73) = ![slabPt (-5/8) (-3/8) (1), slabPt (-3/4) (-3/8) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_74 : (fun k => tauV4 74 k + lamV4 74) = ![slabPt (-7/8) (-3/8) (1), slabPt (-7/8) (-1/4) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_75 : (fun k => tauV4 75 k + lamV4 75) = ![slabPt (-7/8) (-1/8) (1), slabPt (-7/8) (-1/4) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_76 : (fun k => tauV4 76 k + lamV4 76) = ![slabPt (-5/8) (-1/8) (1), slabPt (-5/8) (-1/4) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_77 : (fun k => tauV4 77 k + lamV4 77) = ![slabPt (-5/8) (-3/8) (1), slabPt (-5/8) (-1/4) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_78 : (fun k => tauV4 78 k + lamV4 78) = ![slabPt (-5/8) (-1/8) (1), slabPt (-3/4) (-1/8) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_79 : (fun k => tauV4 79 k + lamV4 79) = ![slabPt (-7/8) (-1/8) (1), slabPt (-3/4) (-1/8) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_80 : (fun k => tauV4 80 k + lamV4 80) = ![slabPt (-3/8) (-3/8) (1), slabPt (-1/4) (-3/8) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_81 : (fun k => tauV4 81 k + lamV4 81) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/4) (-3/8) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_82 : (fun k => tauV4 82 k + lamV4 82) = ![slabPt (-3/8) (-3/8) (1), slabPt (-3/8) (-1/4) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_83 : (fun k => tauV4 83 k + lamV4 83) = ![slabPt (-3/8) (-1/8) (1), slabPt (-3/8) (-1/4) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_84 : (fun k => tauV4 84 k + lamV4 84) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/8) (-1/4) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_85 : (fun k => tauV4 85 k + lamV4 85) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/8) (-1/4) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_86 : (fun k => tauV4 86 k + lamV4 86) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/4) (-1/8) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_87 : (fun k => tauV4 87 k + lamV4 87) = ![slabPt (-3/8) (-1/8) (1), slabPt (-1/4) (-1/8) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_88 : (fun k => tauV4 88 k + lamV4 88) = ![slabPt (-3/8) (-7/8) (1), slabPt (-1/2) (-7/8) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_89 : (fun k => tauV4 89 k + lamV4 89) = ![slabPt (-5/8) (-7/8) (1), slabPt (-1/2) (-7/8) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num


end

end Work.BridgeSquare.SlabBuild

