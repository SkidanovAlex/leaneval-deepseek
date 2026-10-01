import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Infra
import Submission.Work.BridgeSquare.SlabBuild.Collar0_p1
import Submission.Work.BridgeSquare.SlabBuild.Collar0_p2

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

theorem tS0_27 : (fun k => tauV0 27 k + lamV0 27) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/2) (-3/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS0_28 : (fun k => tauV0 28 k + lamV0 28) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS0_29 : (fun k => tauV0 29 k + lamV0 29) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (3/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS0_30 : (fun k => tauV0 30 k + lamV0 30) = ![slabPt (-3/4) (-3/4) (1), slabPt (-3/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS0_31 : (fun k => tauV0 31 k + lamV0 31) = ![slabPt (-3/4) (-1/4) (1), slabPt (-3/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (3/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem brC0'_0 (i : Fin 3) : B0 (aC0' (0, i)) = vface (k := 1) i (fun k => colTri0 0 k + colLam0 0) := by
  rw [cS0_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_1 (i : Fin 3) : B0 (aC0' (1, i)) = vface (k := 1) i (fun k => colTri0 1 k + colLam0 1) := by
  rw [cS0_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_2 (i : Fin 3) : B0 (aC0' (2, i)) = vface (k := 1) i (fun k => colTri0 2 k + colLam0 2) := by
  rw [cS0_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_3 (i : Fin 3) : B0 (aC0' (3, i)) = vface (k := 1) i (fun k => colTri0 3 k + colLam0 3) := by
  rw [cS0_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_4 (i : Fin 3) : B0 (aC0' (4, i)) = vface (k := 1) i (fun k => colTri0 4 k + colLam0 4) := by
  rw [cS0_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_5 (i : Fin 3) : B0 (aC0' (5, i)) = vface (k := 1) i (fun k => colTri0 5 k + colLam0 5) := by
  rw [cS0_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_6 (i : Fin 3) : B0 (aC0' (6, i)) = vface (k := 1) i (fun k => colTri0 6 k + colLam0 6) := by
  rw [cS0_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_7 (i : Fin 3) : B0 (aC0' (7, i)) = vface (k := 1) i (fun k => colTri0 7 k + colLam0 7) := by
  rw [cS0_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_8 (i : Fin 3) : B0 (aC0' (8, i)) = vface (k := 1) i (fun k => colTri0 8 k + colLam0 8) := by
  rw [cS0_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_9 (i : Fin 3) : B0 (aC0' (9, i)) = vface (k := 1) i (fun k => colTri0 9 k + colLam0 9) := by
  rw [cS0_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_10 (i : Fin 3) : B0 (aC0' (10, i)) = vface (k := 1) i (fun k => colTri0 10 k + colLam0 10) := by
  rw [cS0_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_11 (i : Fin 3) : B0 (aC0' (11, i)) = vface (k := 1) i (fun k => colTri0 11 k + colLam0 11) := by
  rw [cS0_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_12 (i : Fin 3) : B0 (aC0' (12, i)) = vface (k := 1) i (fun k => colTri0 12 k + colLam0 12) := by
  rw [cS0_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_13 (i : Fin 3) : B0 (aC0' (13, i)) = vface (k := 1) i (fun k => colTri0 13 k + colLam0 13) := by
  rw [cS0_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_14 (i : Fin 3) : B0 (aC0' (14, i)) = vface (k := 1) i (fun k => colTri0 14 k + colLam0 14) := by
  rw [cS0_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_15 (i : Fin 3) : B0 (aC0' (15, i)) = vface (k := 1) i (fun k => colTri0 15 k + colLam0 15) := by
  rw [cS0_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_16 (i : Fin 3) : B0 (aC0' (16, i)) = vface (k := 1) i (fun k => colTri0 16 k + colLam0 16) := by
  rw [cS0_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_17 (i : Fin 3) : B0 (aC0' (17, i)) = vface (k := 1) i (fun k => colTri0 17 k + colLam0 17) := by
  rw [cS0_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_18 (i : Fin 3) : B0 (aC0' (18, i)) = vface (k := 1) i (fun k => colTri0 18 k + colLam0 18) := by
  rw [cS0_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_19 (i : Fin 3) : B0 (aC0' (19, i)) = vface (k := 1) i (fun k => colTri0 19 k + colLam0 19) := by
  rw [cS0_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_20 (i : Fin 3) : B0 (aC0' (20, i)) = vface (k := 1) i (fun k => colTri0 20 k + colLam0 20) := by
  rw [cS0_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_21 (i : Fin 3) : B0 (aC0' (21, i)) = vface (k := 1) i (fun k => colTri0 21 k + colLam0 21) := by
  rw [cS0_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_22 (i : Fin 3) : B0 (aC0' (22, i)) = vface (k := 1) i (fun k => colTri0 22 k + colLam0 22) := by
  rw [cS0_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC0'_23 (i : Fin 3) : B0 (aC0' (23, i)) = vface (k := 1) i (fun k => colTri0 23 k + colLam0 23) := by
  rw [cS0_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_0 (i : Fin 3) : B0 (aW0 (0, i)) = vface (k := 1) i (fun k => tauV0 0 k + lamV0 0) := by
  rw [tS0_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_1 (i : Fin 3) : B0 (aW0 (1, i)) = vface (k := 1) i (fun k => tauV0 1 k + lamV0 1) := by
  rw [tS0_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_2 (i : Fin 3) : B0 (aW0 (2, i)) = vface (k := 1) i (fun k => tauV0 2 k + lamV0 2) := by
  rw [tS0_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_3 (i : Fin 3) : B0 (aW0 (3, i)) = vface (k := 1) i (fun k => tauV0 3 k + lamV0 3) := by
  rw [tS0_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_4 (i : Fin 3) : B0 (aW0 (4, i)) = vface (k := 1) i (fun k => tauV0 4 k + lamV0 4) := by
  rw [tS0_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_5 (i : Fin 3) : B0 (aW0 (5, i)) = vface (k := 1) i (fun k => tauV0 5 k + lamV0 5) := by
  rw [tS0_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_6 (i : Fin 3) : B0 (aW0 (6, i)) = vface (k := 1) i (fun k => tauV0 6 k + lamV0 6) := by
  rw [tS0_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_7 (i : Fin 3) : B0 (aW0 (7, i)) = vface (k := 1) i (fun k => tauV0 7 k + lamV0 7) := by
  rw [tS0_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_8 (i : Fin 3) : B0 (aW0 (8, i)) = vface (k := 1) i (fun k => tauV0 8 k + lamV0 8) := by
  rw [tS0_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_9 (i : Fin 3) : B0 (aW0 (9, i)) = vface (k := 1) i (fun k => tauV0 9 k + lamV0 9) := by
  rw [tS0_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_10 (i : Fin 3) : B0 (aW0 (10, i)) = vface (k := 1) i (fun k => tauV0 10 k + lamV0 10) := by
  rw [tS0_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_11 (i : Fin 3) : B0 (aW0 (11, i)) = vface (k := 1) i (fun k => tauV0 11 k + lamV0 11) := by
  rw [tS0_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_12 (i : Fin 3) : B0 (aW0 (12, i)) = vface (k := 1) i (fun k => tauV0 12 k + lamV0 12) := by
  rw [tS0_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_13 (i : Fin 3) : B0 (aW0 (13, i)) = vface (k := 1) i (fun k => tauV0 13 k + lamV0 13) := by
  rw [tS0_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_14 (i : Fin 3) : B0 (aW0 (14, i)) = vface (k := 1) i (fun k => tauV0 14 k + lamV0 14) := by
  rw [tS0_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_15 (i : Fin 3) : B0 (aW0 (15, i)) = vface (k := 1) i (fun k => tauV0 15 k + lamV0 15) := by
  rw [tS0_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_16 (i : Fin 3) : B0 (aW0 (16, i)) = vface (k := 1) i (fun k => tauV0 16 k + lamV0 16) := by
  rw [tS0_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_17 (i : Fin 3) : B0 (aW0 (17, i)) = vface (k := 1) i (fun k => tauV0 17 k + lamV0 17) := by
  rw [tS0_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_18 (i : Fin 3) : B0 (aW0 (18, i)) = vface (k := 1) i (fun k => tauV0 18 k + lamV0 18) := by
  rw [tS0_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_19 (i : Fin 3) : B0 (aW0 (19, i)) = vface (k := 1) i (fun k => tauV0 19 k + lamV0 19) := by
  rw [tS0_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_20 (i : Fin 3) : B0 (aW0 (20, i)) = vface (k := 1) i (fun k => tauV0 20 k + lamV0 20) := by
  rw [tS0_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_21 (i : Fin 3) : B0 (aW0 (21, i)) = vface (k := 1) i (fun k => tauV0 21 k + lamV0 21) := by
  rw [tS0_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_22 (i : Fin 3) : B0 (aW0 (22, i)) = vface (k := 1) i (fun k => tauV0 22 k + lamV0 22) := by
  rw [tS0_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_23 (i : Fin 3) : B0 (aW0 (23, i)) = vface (k := 1) i (fun k => tauV0 23 k + lamV0 23) := by
  rw [tS0_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_24 (i : Fin 3) : B0 (aW0 (24, i)) = vface (k := 1) i (fun k => tauV0 24 k + lamV0 24) := by
  rw [tS0_24]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_25 (i : Fin 3) : B0 (aW0 (25, i)) = vface (k := 1) i (fun k => tauV0 25 k + lamV0 25) := by
  rw [tS0_25]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_26 (i : Fin 3) : B0 (aW0 (26, i)) = vface (k := 1) i (fun k => tauV0 26 k + lamV0 26) := by
  rw [tS0_26]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_27 (i : Fin 3) : B0 (aW0 (27, i)) = vface (k := 1) i (fun k => tauV0 27 k + lamV0 27) := by
  rw [tS0_27]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_28 (i : Fin 3) : B0 (aW0 (28, i)) = vface (k := 1) i (fun k => tauV0 28 k + lamV0 28) := by
  rw [tS0_28]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_29 (i : Fin 3) : B0 (aW0 (29, i)) = vface (k := 1) i (fun k => tauV0 29 k + lamV0 29) := by
  rw [tS0_29]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_30 (i : Fin 3) : B0 (aW0 (30, i)) = vface (k := 1) i (fun k => tauV0 30 k + lamV0 30) := by
  rw [tS0_30]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW0_31 (i : Fin 3) : B0 (aW0 (31, i)) = vface (k := 1) i (fun k => tauV0 31 k + lamV0 31) := by
  rw [tS0_31]; fin_cases i <;> funext k <;> fin_cases k <;> rfl

/-- The atoms of the second edge family of the collar. -/
theorem brC0' : ∀ p : Fin 24 × Fin 3,
    B0 (aC0' p) = vface (k := 1) p.2 (fun k => colTri0 p.1 k + colLam0 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brC0'_0 i, brC0'_1 i, brC0'_2 i, brC0'_3 i, brC0'_4 i, brC0'_5 i, brC0'_6 i, brC0'_7 i, brC0'_8 i, brC0'_9 i, brC0'_10 i, brC0'_11 i, brC0'_12 i, brC0'_13 i, brC0'_14 i, brC0'_15 i, brC0'_16 i, brC0'_17 i, brC0'_18 i, brC0'_19 i, brC0'_20 i, brC0'_21 i, brC0'_22 i, brC0'_23 i]

/-- The atoms of the edges of the wall. -/
theorem brW0 : ∀ p : Fin 32 × Fin 3,
    B0 (aW0 p) = vface (k := 1) p.2 (fun k => tauV0 p.1 k + lamV0 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brW0_0 i, brW0_1 i, brW0_2 i, brW0_3 i, brW0_4 i, brW0_5 i, brW0_6 i, brW0_7 i, brW0_8 i, brW0_9 i, brW0_10 i, brW0_11 i, brW0_12 i, brW0_13 i, brW0_14 i, brW0_15 i, brW0_16 i, brW0_17 i, brW0_18 i, brW0_19 i, brW0_20 i, brW0_21 i, brW0_22 i, brW0_23 i, brW0_24 i, brW0_25 i, brW0_26 i, brW0_27 i, brW0_28 i, brW0_29 i, brW0_30 i, brW0_31 i]

/-- The atoms of the first coarse triangle. -/
theorem brB00 : ∀ i : Fin 3, B0 (aB00 i) = vface (k := 1) i botV0 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

/-- The atoms of the second coarse triangle. -/
theorem brB01 : ∀ i : Fin 3, B0 (aB01 i) = vface (k := 1) i botV1 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

theorem colLam_mem0 (j : NCol0) : slabL 0 (colLam0 j) ∈ Work.Cusp.lattice 0 := by
  have h : slabL 0 (colLam0 j) ∈ ({Work.Cusp.kv 0 1, Work.Cusp.kv 0 2} : Set CuspE3) := by
    fin_cases j <;> simp [colLam0, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3]
  rcases h with h | h
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 1)
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 2)

/-- **The collar of cusp `0` is in the kernel of `slabChain`.** -/
theorem collar_slab0 : slabChain 0 2 (collarChain0 : AffC 2) = 0 := by
  rw [collarChain0, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, map_sub, slabChain_single_one, slabChain_single_one]
  have h1 : slabV 0 (fun k => colTri0 j k + colLam0 j)
      = fun k => slabV 0 (colTri0 j) k + slabL 0 (colLam0 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 0 (slabV 0 (colTri0 j)) (slabL 0 (colLam0 j))
        (colLam_mem0 j), sub_self, smul_zero]

/-- **The boundary of the collar of cusp `0`.** -/
theorem dLC_collar0 :
    dLC 1 (collarChain0 : AffC 2) = dLC 1 (wallChain0 : AffC 2) - dLC 1 slabBot := by
  have hP1 : (∑ j : NCol0, dLC 1 (colCoef0 j • Finsupp.single (colTri0 j) (1 : ℤ)))
      = ∑ p : Fin 24 × Fin 3, cC0 p • X0 (aC0 p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC0, ← smul_smul, ← brC0 (j, i)]
  have hP2 : (∑ j : NCol0, dLC 1 (colCoef0 j •
        Finsupp.single (fun k => colTri0 j k + colLam0 j) (1 : ℤ)))
      = ∑ p : Fin 24 × Fin 3, cC0' p • X0 (aC0' p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC0', ← smul_smul, ← brC0' (j, i)]
  have hQ1 : (∑ p : Fin 24 × Fin 3, cC0 p • X0 (aC0 p))
      = ∑ l : Fin Nat0, D10 l • X0 l :=
    sum_smul_regroup aC0 cC0 X0
  have hQ2 : (∑ p : Fin 24 × Fin 3, cC0' p • X0 (aC0' p))
      = ∑ l : Fin Nat0, D20 l • X0 l :=
    sum_smul_regroup aC0' cC0' X0
  have hW : (∑ p : Fin 32 × Fin 3, cW0 p • X0 (aW0 p))
      = ∑ l : Fin Nat0, D30 l • X0 l :=
    sum_smul_regroup aW0 cW0 X0
  have hB0 : (∑ i : Fin 3, cB0 i • X0 (aB00 i))
      = ∑ l : Fin Nat0, D40 l • X0 l :=
    sum_smul_regroup aB00 cB0 X0
  have hB1 : (∑ i : Fin 3, cB0 i • X0 (aB01 i))
      = ∑ l : Fin Nat0, D50 l • X0 l :=
    sum_smul_regroup aB01 cB0 X0
  have hwall : dLC 1 (wallChain0 : AffC 2)
      = ∑ p : Fin 32 × Fin 3, cW0 p • X0 (aW0 p) := by
    rw [wallChain0, map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cW0, ← smul_smul, ← brW0 (j, i)]
  have hbot : dLC 1 slabBot
      = (∑ i : Fin 3, cB0 i • X0 (aB00 i))
        - (∑ i : Fin 3, cB0 i • X0 (aB01 i)) := by
    rw [slabBot, map_sub, dLC_single, dLC_single]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB0, ← brB00 i]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB0, ← brB01 i]
  have hcol : dLC 1 (collarChain0 : AffC 2)
      = (∑ j : NCol0, dLC 1 (colCoef0 j • Finsupp.single (colTri0 j) (1 : ℤ)))
        - (∑ j : NCol0, dLC 1 (colCoef0 j •
            Finsupp.single (fun k => colTri0 j k + colLam0 j) (1 : ℤ))) := by
    rw [collarChain0, map_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_sub, smul_sub, map_smul, map_smul]
  have hcoef : ∀ l : Fin Nat0, D10 l - D20 l = D30 l - (D40 l - D50 l) := hcoef0
  rw [hcol, hP1, hP2, hQ1, hQ2, hwall, hW, hbot, hB0, hB1]
  exact sum_smul_four D10 D20 D30 D40 D50 X0 hcoef

end

end Work.BridgeSquare.SlabBuild

