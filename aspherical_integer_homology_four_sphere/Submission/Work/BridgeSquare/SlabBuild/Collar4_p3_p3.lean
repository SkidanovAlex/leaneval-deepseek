import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Collar4_p1
import Submission.Work.BridgeSquare.SlabBuild.Collar4_p2
import Submission.Work.BridgeSquare.SlabBuild.Collar4_p3_p1
import Submission.Work.BridgeSquare.SlabBuild.Collar4_p3_p2

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

theorem brW4_62 (i : Fin 3) : B4 (aW4 (62, i)) = vface (k := 1) i (fun k => tauV4 62 k + lamV4 62) := by
  rw [tS4_62]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_63 (i : Fin 3) : B4 (aW4 (63, i)) = vface (k := 1) i (fun k => tauV4 63 k + lamV4 63) := by
  rw [tS4_63]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_64 (i : Fin 3) : B4 (aW4 (64, i)) = vface (k := 1) i (fun k => tauV4 64 k + lamV4 64) := by
  rw [tS4_64]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_65 (i : Fin 3) : B4 (aW4 (65, i)) = vface (k := 1) i (fun k => tauV4 65 k + lamV4 65) := by
  rw [tS4_65]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_66 (i : Fin 3) : B4 (aW4 (66, i)) = vface (k := 1) i (fun k => tauV4 66 k + lamV4 66) := by
  rw [tS4_66]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_67 (i : Fin 3) : B4 (aW4 (67, i)) = vface (k := 1) i (fun k => tauV4 67 k + lamV4 67) := by
  rw [tS4_67]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_68 (i : Fin 3) : B4 (aW4 (68, i)) = vface (k := 1) i (fun k => tauV4 68 k + lamV4 68) := by
  rw [tS4_68]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_69 (i : Fin 3) : B4 (aW4 (69, i)) = vface (k := 1) i (fun k => tauV4 69 k + lamV4 69) := by
  rw [tS4_69]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_70 (i : Fin 3) : B4 (aW4 (70, i)) = vface (k := 1) i (fun k => tauV4 70 k + lamV4 70) := by
  rw [tS4_70]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_71 (i : Fin 3) : B4 (aW4 (71, i)) = vface (k := 1) i (fun k => tauV4 71 k + lamV4 71) := by
  rw [tS4_71]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_72 (i : Fin 3) : B4 (aW4 (72, i)) = vface (k := 1) i (fun k => tauV4 72 k + lamV4 72) := by
  rw [tS4_72]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_73 (i : Fin 3) : B4 (aW4 (73, i)) = vface (k := 1) i (fun k => tauV4 73 k + lamV4 73) := by
  rw [tS4_73]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_74 (i : Fin 3) : B4 (aW4 (74, i)) = vface (k := 1) i (fun k => tauV4 74 k + lamV4 74) := by
  rw [tS4_74]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_75 (i : Fin 3) : B4 (aW4 (75, i)) = vface (k := 1) i (fun k => tauV4 75 k + lamV4 75) := by
  rw [tS4_75]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_76 (i : Fin 3) : B4 (aW4 (76, i)) = vface (k := 1) i (fun k => tauV4 76 k + lamV4 76) := by
  rw [tS4_76]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_77 (i : Fin 3) : B4 (aW4 (77, i)) = vface (k := 1) i (fun k => tauV4 77 k + lamV4 77) := by
  rw [tS4_77]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_78 (i : Fin 3) : B4 (aW4 (78, i)) = vface (k := 1) i (fun k => tauV4 78 k + lamV4 78) := by
  rw [tS4_78]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_79 (i : Fin 3) : B4 (aW4 (79, i)) = vface (k := 1) i (fun k => tauV4 79 k + lamV4 79) := by
  rw [tS4_79]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_80 (i : Fin 3) : B4 (aW4 (80, i)) = vface (k := 1) i (fun k => tauV4 80 k + lamV4 80) := by
  rw [tS4_80]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_81 (i : Fin 3) : B4 (aW4 (81, i)) = vface (k := 1) i (fun k => tauV4 81 k + lamV4 81) := by
  rw [tS4_81]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_82 (i : Fin 3) : B4 (aW4 (82, i)) = vface (k := 1) i (fun k => tauV4 82 k + lamV4 82) := by
  rw [tS4_82]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_83 (i : Fin 3) : B4 (aW4 (83, i)) = vface (k := 1) i (fun k => tauV4 83 k + lamV4 83) := by
  rw [tS4_83]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_84 (i : Fin 3) : B4 (aW4 (84, i)) = vface (k := 1) i (fun k => tauV4 84 k + lamV4 84) := by
  rw [tS4_84]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_85 (i : Fin 3) : B4 (aW4 (85, i)) = vface (k := 1) i (fun k => tauV4 85 k + lamV4 85) := by
  rw [tS4_85]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_86 (i : Fin 3) : B4 (aW4 (86, i)) = vface (k := 1) i (fun k => tauV4 86 k + lamV4 86) := by
  rw [tS4_86]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_87 (i : Fin 3) : B4 (aW4 (87, i)) = vface (k := 1) i (fun k => tauV4 87 k + lamV4 87) := by
  rw [tS4_87]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_88 (i : Fin 3) : B4 (aW4 (88, i)) = vface (k := 1) i (fun k => tauV4 88 k + lamV4 88) := by
  rw [tS4_88]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_89 (i : Fin 3) : B4 (aW4 (89, i)) = vface (k := 1) i (fun k => tauV4 89 k + lamV4 89) := by
  rw [tS4_89]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_90 (i : Fin 3) : B4 (aW4 (90, i)) = vface (k := 1) i (fun k => tauV4 90 k + lamV4 90) := by
  rw [tS4_90]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_91 (i : Fin 3) : B4 (aW4 (91, i)) = vface (k := 1) i (fun k => tauV4 91 k + lamV4 91) := by
  rw [tS4_91]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_92 (i : Fin 3) : B4 (aW4 (92, i)) = vface (k := 1) i (fun k => tauV4 92 k + lamV4 92) := by
  rw [tS4_92]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_93 (i : Fin 3) : B4 (aW4 (93, i)) = vface (k := 1) i (fun k => tauV4 93 k + lamV4 93) := by
  rw [tS4_93]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_94 (i : Fin 3) : B4 (aW4 (94, i)) = vface (k := 1) i (fun k => tauV4 94 k + lamV4 94) := by
  rw [tS4_94]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_95 (i : Fin 3) : B4 (aW4 (95, i)) = vface (k := 1) i (fun k => tauV4 95 k + lamV4 95) := by
  rw [tS4_95]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_96 (i : Fin 3) : B4 (aW4 (96, i)) = vface (k := 1) i (fun k => tauV4 96 k + lamV4 96) := by
  rw [tS4_96]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_97 (i : Fin 3) : B4 (aW4 (97, i)) = vface (k := 1) i (fun k => tauV4 97 k + lamV4 97) := by
  rw [tS4_97]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_98 (i : Fin 3) : B4 (aW4 (98, i)) = vface (k := 1) i (fun k => tauV4 98 k + lamV4 98) := by
  rw [tS4_98]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_99 (i : Fin 3) : B4 (aW4 (99, i)) = vface (k := 1) i (fun k => tauV4 99 k + lamV4 99) := by
  rw [tS4_99]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_100 (i : Fin 3) : B4 (aW4 (100, i)) = vface (k := 1) i (fun k => tauV4 100 k + lamV4 100) := by
  rw [tS4_100]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_101 (i : Fin 3) : B4 (aW4 (101, i)) = vface (k := 1) i (fun k => tauV4 101 k + lamV4 101) := by
  rw [tS4_101]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_102 (i : Fin 3) : B4 (aW4 (102, i)) = vface (k := 1) i (fun k => tauV4 102 k + lamV4 102) := by
  rw [tS4_102]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_103 (i : Fin 3) : B4 (aW4 (103, i)) = vface (k := 1) i (fun k => tauV4 103 k + lamV4 103) := by
  rw [tS4_103]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_104 (i : Fin 3) : B4 (aW4 (104, i)) = vface (k := 1) i (fun k => tauV4 104 k + lamV4 104) := by
  rw [tS4_104]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_105 (i : Fin 3) : B4 (aW4 (105, i)) = vface (k := 1) i (fun k => tauV4 105 k + lamV4 105) := by
  rw [tS4_105]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_106 (i : Fin 3) : B4 (aW4 (106, i)) = vface (k := 1) i (fun k => tauV4 106 k + lamV4 106) := by
  rw [tS4_106]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_107 (i : Fin 3) : B4 (aW4 (107, i)) = vface (k := 1) i (fun k => tauV4 107 k + lamV4 107) := by
  rw [tS4_107]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_108 (i : Fin 3) : B4 (aW4 (108, i)) = vface (k := 1) i (fun k => tauV4 108 k + lamV4 108) := by
  rw [tS4_108]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_109 (i : Fin 3) : B4 (aW4 (109, i)) = vface (k := 1) i (fun k => tauV4 109 k + lamV4 109) := by
  rw [tS4_109]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_110 (i : Fin 3) : B4 (aW4 (110, i)) = vface (k := 1) i (fun k => tauV4 110 k + lamV4 110) := by
  rw [tS4_110]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_111 (i : Fin 3) : B4 (aW4 (111, i)) = vface (k := 1) i (fun k => tauV4 111 k + lamV4 111) := by
  rw [tS4_111]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_112 (i : Fin 3) : B4 (aW4 (112, i)) = vface (k := 1) i (fun k => tauV4 112 k + lamV4 112) := by
  rw [tS4_112]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_113 (i : Fin 3) : B4 (aW4 (113, i)) = vface (k := 1) i (fun k => tauV4 113 k + lamV4 113) := by
  rw [tS4_113]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_114 (i : Fin 3) : B4 (aW4 (114, i)) = vface (k := 1) i (fun k => tauV4 114 k + lamV4 114) := by
  rw [tS4_114]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_115 (i : Fin 3) : B4 (aW4 (115, i)) = vface (k := 1) i (fun k => tauV4 115 k + lamV4 115) := by
  rw [tS4_115]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_116 (i : Fin 3) : B4 (aW4 (116, i)) = vface (k := 1) i (fun k => tauV4 116 k + lamV4 116) := by
  rw [tS4_116]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_117 (i : Fin 3) : B4 (aW4 (117, i)) = vface (k := 1) i (fun k => tauV4 117 k + lamV4 117) := by
  rw [tS4_117]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_118 (i : Fin 3) : B4 (aW4 (118, i)) = vface (k := 1) i (fun k => tauV4 118 k + lamV4 118) := by
  rw [tS4_118]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_119 (i : Fin 3) : B4 (aW4 (119, i)) = vface (k := 1) i (fun k => tauV4 119 k + lamV4 119) := by
  rw [tS4_119]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_120 (i : Fin 3) : B4 (aW4 (120, i)) = vface (k := 1) i (fun k => tauV4 120 k + lamV4 120) := by
  rw [tS4_120]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_121 (i : Fin 3) : B4 (aW4 (121, i)) = vface (k := 1) i (fun k => tauV4 121 k + lamV4 121) := by
  rw [tS4_121]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_122 (i : Fin 3) : B4 (aW4 (122, i)) = vface (k := 1) i (fun k => tauV4 122 k + lamV4 122) := by
  rw [tS4_122]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_123 (i : Fin 3) : B4 (aW4 (123, i)) = vface (k := 1) i (fun k => tauV4 123 k + lamV4 123) := by
  rw [tS4_123]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_124 (i : Fin 3) : B4 (aW4 (124, i)) = vface (k := 1) i (fun k => tauV4 124 k + lamV4 124) := by
  rw [tS4_124]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_125 (i : Fin 3) : B4 (aW4 (125, i)) = vface (k := 1) i (fun k => tauV4 125 k + lamV4 125) := by
  rw [tS4_125]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_126 (i : Fin 3) : B4 (aW4 (126, i)) = vface (k := 1) i (fun k => tauV4 126 k + lamV4 126) := by
  rw [tS4_126]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_127 (i : Fin 3) : B4 (aW4 (127, i)) = vface (k := 1) i (fun k => tauV4 127 k + lamV4 127) := by
  rw [tS4_127]; fin_cases i <;> funext k <;> fin_cases k <;> rfl

/-- The atoms of the second edge family of the collar. -/
theorem brC4' : ∀ p : Fin 48 × Fin 3,
    B4 (aC4' p) = vface (k := 1) p.2 (fun k => colTri4 p.1 k + colLam4 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brC4'_0 i, brC4'_1 i, brC4'_2 i, brC4'_3 i, brC4'_4 i, brC4'_5 i, brC4'_6 i, brC4'_7 i, brC4'_8 i, brC4'_9 i, brC4'_10 i, brC4'_11 i, brC4'_12 i, brC4'_13 i, brC4'_14 i, brC4'_15 i, brC4'_16 i, brC4'_17 i, brC4'_18 i, brC4'_19 i, brC4'_20 i, brC4'_21 i, brC4'_22 i, brC4'_23 i, brC4'_24 i, brC4'_25 i, brC4'_26 i, brC4'_27 i, brC4'_28 i, brC4'_29 i, brC4'_30 i, brC4'_31 i, brC4'_32 i, brC4'_33 i, brC4'_34 i, brC4'_35 i, brC4'_36 i, brC4'_37 i, brC4'_38 i, brC4'_39 i, brC4'_40 i, brC4'_41 i, brC4'_42 i, brC4'_43 i, brC4'_44 i, brC4'_45 i, brC4'_46 i, brC4'_47 i]

/-- The atoms of the edges of the wall. -/
theorem brW4 : ∀ p : Fin 128 × Fin 3,
    B4 (aW4 p) = vface (k := 1) p.2 (fun k => tauV4 p.1 k + lamV4 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brW4_0 i, brW4_1 i, brW4_2 i, brW4_3 i, brW4_4 i, brW4_5 i, brW4_6 i, brW4_7 i, brW4_8 i, brW4_9 i, brW4_10 i, brW4_11 i, brW4_12 i, brW4_13 i, brW4_14 i, brW4_15 i, brW4_16 i, brW4_17 i, brW4_18 i, brW4_19 i, brW4_20 i, brW4_21 i, brW4_22 i, brW4_23 i, brW4_24 i, brW4_25 i, brW4_26 i, brW4_27 i, brW4_28 i, brW4_29 i, brW4_30 i, brW4_31 i, brW4_32 i, brW4_33 i, brW4_34 i, brW4_35 i, brW4_36 i, brW4_37 i, brW4_38 i, brW4_39 i, brW4_40 i, brW4_41 i, brW4_42 i, brW4_43 i, brW4_44 i, brW4_45 i, brW4_46 i, brW4_47 i, brW4_48 i, brW4_49 i, brW4_50 i, brW4_51 i, brW4_52 i, brW4_53 i, brW4_54 i, brW4_55 i, brW4_56 i, brW4_57 i, brW4_58 i, brW4_59 i, brW4_60 i, brW4_61 i, brW4_62 i, brW4_63 i, brW4_64 i, brW4_65 i, brW4_66 i, brW4_67 i, brW4_68 i, brW4_69 i, brW4_70 i, brW4_71 i, brW4_72 i, brW4_73 i, brW4_74 i, brW4_75 i, brW4_76 i, brW4_77 i, brW4_78 i, brW4_79 i, brW4_80 i, brW4_81 i, brW4_82 i, brW4_83 i, brW4_84 i, brW4_85 i, brW4_86 i, brW4_87 i, brW4_88 i, brW4_89 i, brW4_90 i, brW4_91 i, brW4_92 i, brW4_93 i, brW4_94 i, brW4_95 i, brW4_96 i, brW4_97 i, brW4_98 i, brW4_99 i, brW4_100 i, brW4_101 i, brW4_102 i, brW4_103 i, brW4_104 i, brW4_105 i, brW4_106 i, brW4_107 i, brW4_108 i, brW4_109 i, brW4_110 i, brW4_111 i, brW4_112 i, brW4_113 i, brW4_114 i, brW4_115 i, brW4_116 i, brW4_117 i, brW4_118 i, brW4_119 i, brW4_120 i, brW4_121 i, brW4_122 i, brW4_123 i, brW4_124 i, brW4_125 i, brW4_126 i, brW4_127 i]

/-- The atoms of the first coarse triangle. -/
theorem brB40 : ∀ i : Fin 3, B4 (aB40 i) = vface (k := 1) i botV0 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

/-- The atoms of the second coarse triangle. -/
theorem brB41 : ∀ i : Fin 3, B4 (aB41 i) = vface (k := 1) i botV1 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

theorem colLam_mem4 (j : NCol4) : slabL 4 (colLam4 j) ∈ Work.Cusp.lattice 4 := by
  have h : slabL 4 (colLam4 j) ∈ ({Work.Cusp.kv 4 1, Work.Cusp.kv 4 2} : Set CuspE3) := by
    fin_cases j <;> simp [colLam4, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3]
  rcases h with h | h
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 1)
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 2)

/-- **The collar of cusp `4` is in the kernel of `slabChain`.** -/
theorem collar_slab4 : slabChain 4 2 (collarChain4 : AffC 2) = 0 := by
  rw [collarChain4, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, map_sub, slabChain_single_one, slabChain_single_one]
  have h1 : slabV 4 (fun k => colTri4 j k + colLam4 j)
      = fun k => slabV 4 (colTri4 j) k + slabL 4 (colLam4 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 4 (slabV 4 (colTri4 j)) (slabL 4 (colLam4 j))
        (colLam_mem4 j), sub_self, smul_zero]

/-- **The boundary of the collar of cusp `4`.** -/
theorem dLC_collar4 :
    dLC 1 (collarChain4 : AffC 2) = dLC 1 (wallChain4 : AffC 2) - dLC 1 slabBot := by
  have hP1 : (∑ j : NCol4, dLC 1 (colCoef4 j • Finsupp.single (colTri4 j) (1 : ℤ)))
      = ∑ p : Fin 48 × Fin 3, cC4 p • X4 (aC4 p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC4, ← smul_smul, ← brC4 (j, i)]
  have hP2 : (∑ j : NCol4, dLC 1 (colCoef4 j •
        Finsupp.single (fun k => colTri4 j k + colLam4 j) (1 : ℤ)))
      = ∑ p : Fin 48 × Fin 3, cC4' p • X4 (aC4' p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC4', ← smul_smul, ← brC4' (j, i)]
  have hQ1 : (∑ p : Fin 48 × Fin 3, cC4 p • X4 (aC4 p))
      = ∑ l : Fin Nat4, D14 l • X4 l :=
    sum_smul_regroup aC4 cC4 X4
  have hQ2 : (∑ p : Fin 48 × Fin 3, cC4' p • X4 (aC4' p))
      = ∑ l : Fin Nat4, D24 l • X4 l :=
    sum_smul_regroup aC4' cC4' X4
  have hW : (∑ p : Fin 128 × Fin 3, cW4 p • X4 (aW4 p))
      = ∑ l : Fin Nat4, D34 l • X4 l :=
    sum_smul_regroup aW4 cW4 X4
  have hB0 : (∑ i : Fin 3, cB4 i • X4 (aB40 i))
      = ∑ l : Fin Nat4, D44 l • X4 l :=
    sum_smul_regroup aB40 cB4 X4
  have hB1 : (∑ i : Fin 3, cB4 i • X4 (aB41 i))
      = ∑ l : Fin Nat4, D54 l • X4 l :=
    sum_smul_regroup aB41 cB4 X4
  have hwall : dLC 1 (wallChain4 : AffC 2)
      = ∑ p : Fin 128 × Fin 3, cW4 p • X4 (aW4 p) := by
    rw [wallChain4, map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cW4, ← smul_smul, ← brW4 (j, i)]
  have hbot : dLC 1 slabBot
      = (∑ i : Fin 3, cB4 i • X4 (aB40 i))
        - (∑ i : Fin 3, cB4 i • X4 (aB41 i)) := by
    rw [slabBot, map_sub, dLC_single, dLC_single]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB4, ← brB40 i]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB4, ← brB41 i]
  have hcol : dLC 1 (collarChain4 : AffC 2)
      = (∑ j : NCol4, dLC 1 (colCoef4 j • Finsupp.single (colTri4 j) (1 : ℤ)))
        - (∑ j : NCol4, dLC 1 (colCoef4 j •
            Finsupp.single (fun k => colTri4 j k + colLam4 j) (1 : ℤ))) := by
    rw [collarChain4, map_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_sub, smul_sub, map_smul, map_smul]
  have hcoef : ∀ l : Fin Nat4, D14 l - D24 l = D34 l - (D44 l - D54 l) := hcoef4
  rw [hcol, hP1, hP2, hQ1, hQ2, hwall, hW, hbot, hB0, hB1]
  exact sum_smul_four D14 D24 D34 D44 D54 X4 hcoef

end

end Work.BridgeSquare.SlabBuild

