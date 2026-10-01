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



end

end Work.BridgeSquare.SlabBuild

