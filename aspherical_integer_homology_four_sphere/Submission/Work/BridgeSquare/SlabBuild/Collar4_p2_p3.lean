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

