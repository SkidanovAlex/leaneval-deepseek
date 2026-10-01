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



end

end Work.BridgeSquare.SlabBuild

