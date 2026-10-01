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

theorem tS4_90 : (fun k => tauV4 90 k + lamV4 90) = ![slabPt (-3/8) (-7/8) (1), slabPt (-3/8) (-3/4) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_91 : (fun k => tauV4 91 k + lamV4 91) = ![slabPt (-3/8) (-5/8) (1), slabPt (-3/8) (-3/4) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_92 : (fun k => tauV4 92 k + lamV4 92) = ![slabPt (-5/8) (-5/8) (1), slabPt (-5/8) (-3/4) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_93 : (fun k => tauV4 93 k + lamV4 93) = ![slabPt (-5/8) (-7/8) (1), slabPt (-5/8) (-3/4) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_94 : (fun k => tauV4 94 k + lamV4 94) = ![slabPt (-5/8) (-5/8) (1), slabPt (-1/2) (-5/8) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_95 : (fun k => tauV4 95 k + lamV4 95) = ![slabPt (-3/8) (-5/8) (1), slabPt (-1/2) (-5/8) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_96 : (fun k => tauV4 96 k + lamV4 96) = ![slabPt (-7/8) (-3/8) (1), slabPt (-3/4) (-3/8) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_97 : (fun k => tauV4 97 k + lamV4 97) = ![slabPt (-5/8) (-3/8) (1), slabPt (-3/4) (-3/8) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_98 : (fun k => tauV4 98 k + lamV4 98) = ![slabPt (-7/8) (-3/8) (1), slabPt (-7/8) (-1/2) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_99 : (fun k => tauV4 99 k + lamV4 99) = ![slabPt (-7/8) (-5/8) (1), slabPt (-7/8) (-1/2) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_100 : (fun k => tauV4 100 k + lamV4 100) = ![slabPt (-5/8) (-5/8) (1), slabPt (-5/8) (-1/2) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_101 : (fun k => tauV4 101 k + lamV4 101) = ![slabPt (-5/8) (-3/8) (1), slabPt (-5/8) (-1/2) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_102 : (fun k => tauV4 102 k + lamV4 102) = ![slabPt (-5/8) (-5/8) (1), slabPt (-3/4) (-5/8) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_103 : (fun k => tauV4 103 k + lamV4 103) = ![slabPt (-7/8) (-5/8) (1), slabPt (-3/4) (-5/8) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_104 : (fun k => tauV4 104 k + lamV4 104) = ![slabPt (-3/8) (-3/8) (1), slabPt (-1/4) (-3/8) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_105 : (fun k => tauV4 105 k + lamV4 105) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/4) (-3/8) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_106 : (fun k => tauV4 106 k + lamV4 106) = ![slabPt (-3/8) (-3/8) (1), slabPt (-3/8) (-1/2) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_107 : (fun k => tauV4 107 k + lamV4 107) = ![slabPt (-3/8) (-5/8) (1), slabPt (-3/8) (-1/2) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_108 : (fun k => tauV4 108 k + lamV4 108) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/8) (-1/2) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_109 : (fun k => tauV4 109 k + lamV4 109) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/8) (-1/2) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_110 : (fun k => tauV4 110 k + lamV4 110) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/4) (-5/8) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_111 : (fun k => tauV4 111 k + lamV4 111) = ![slabPt (-3/8) (-5/8) (1), slabPt (-1/4) (-5/8) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_112 : (fun k => tauV4 112 k + lamV4 112) = ![slabPt (-3/8) (-3/8) (1), slabPt (-1/2) (-3/8) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_113 : (fun k => tauV4 113 k + lamV4 113) = ![slabPt (-5/8) (-3/8) (1), slabPt (-1/2) (-3/8) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_114 : (fun k => tauV4 114 k + lamV4 114) = ![slabPt (-3/8) (-3/8) (1), slabPt (-3/8) (-1/4) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_115 : (fun k => tauV4 115 k + lamV4 115) = ![slabPt (-3/8) (-1/8) (1), slabPt (-3/8) (-1/4) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_116 : (fun k => tauV4 116 k + lamV4 116) = ![slabPt (-5/8) (-1/8) (1), slabPt (-5/8) (-1/4) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_117 : (fun k => tauV4 117 k + lamV4 117) = ![slabPt (-5/8) (-3/8) (1), slabPt (-5/8) (-1/4) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_118 : (fun k => tauV4 118 k + lamV4 118) = ![slabPt (-5/8) (-1/8) (1), slabPt (-1/2) (-1/8) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_119 : (fun k => tauV4 119 k + lamV4 119) = ![slabPt (-3/8) (-1/8) (1), slabPt (-1/2) (-1/8) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num


end

end Work.BridgeSquare.SlabBuild

