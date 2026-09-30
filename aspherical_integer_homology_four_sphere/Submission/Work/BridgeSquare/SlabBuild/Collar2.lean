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

/-! ## The collar identity of cusp `2`

`D1`..`D5`  are the coefficient tables of the five pieces of the identity
`dLC 1 collarChain2 = dLC 1 wallChain2 - dLC 1 slabBot`, indexed by the *atoms* (the
directed edges) `B2`, and `aC2`..`aB21` are the atom of each slot of each piece.  The
identity is then the pointwise identity of the coefficients `D1 - D2 = D3 - (D4 - D5)`.
-/

/-- The number of distinct atoms of the collar identity of cusp `2`. -/
abbrev Nat2 : ℕ := 114
/-- The atoms (directed edges) of the collar identity of cusp `2`. -/
def B2 : Fin Nat2 → (Fin 2 → CuspE3) :=
  ![![slabPt (-1/2) (-1/2) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-1/2) (-1/2) 1, slabPt (-1/4) (-3/4) 1],
    ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/4) 1],
    ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-1/2) (-1/4) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-1/2) (-1/4) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-1/2) (-3/4) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-1/2) (-3/4) 1, slabPt (-1/4) (-3/4) 1],
    ![slabPt (-1/2) (-3/4) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-1/2) (-3/4) 1, slabPt (0) (0) 0],
    ![slabPt (-1/2) (0) 1, slabPt (-3/4) (0) 1],
    ![slabPt (-1/2) (0) 1, slabPt (-3/4) (1/4) 1],
    ![slabPt (-1/2) (1/2) 1, slabPt (-1/2) (1/4) 1],
    ![slabPt (-1/2) (1/2) 1, slabPt (-1/4) (1/4) 1],
    ![slabPt (-1/2) (1/2) 1, slabPt (-3/4) (1/4) 1],
    ![slabPt (-1/2) (1/4) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-1/2) (1/4) 1, slabPt (-1/4) (1/4) 1],
    ![slabPt (-1/2) (1/4) 1, slabPt (-3/4) (1/4) 1],
    ![slabPt (-1/2) (1/4) 1, slabPt (0) (1) 0],
    ![slabPt (-1/4) (-1/2) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-1/4) (-1/2) 1, slabPt (0) (-1/2) 1],
    ![slabPt (-1/4) (-1/4) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-1/4) (-1/4) 1, slabPt (-1/2) (-1/4) 1],
    ![slabPt (-1/4) (-1/4) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (-1/2) 1],
    ![slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1],
    ![slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/2) 1],
    ![slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1],
    ![slabPt (-1/4) (-1/4) 1, slabPt (0) (0) 1],
    ![slabPt (-1/4) (-3/4) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-1/4) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-1/4) (-3/4) 1, slabPt (-1/4) (-1/2) 1],
    ![slabPt (-1/4) (-3/4) 1, slabPt (0) (-1/2) 1],
    ![slabPt (-1/4) (-3/4) 1, slabPt (0) (-3/4) 1],
    ![slabPt (-1/4) (-3/4) 1, slabPt (0) (0) 0],
    ![slabPt (-1/4) (-3/4) 1, slabPt (1/4) (-3/4) 1],
    ![slabPt (-1/4) (0) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-1/4) (0) 1, slabPt (0) (0) 1],
    ![slabPt (-1/4) (1/4) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1],
    ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1],
    ![slabPt (-1/4) (1/4) 1, slabPt (0) (0) 1],
    ![slabPt (-1/4) (1/4) 1, slabPt (0) (1) 0],
    ![slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1],
    ![slabPt (-1/4) (1/4) 1, slabPt (1/4) (1/4) 1],
    ![slabPt (-3/4) (-1/2) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-1/4) 1],
    ![slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-3/4) (-1/2) 1, slabPt (0) (0) 0],
    ![slabPt (-3/4) (-1/4) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-3/4) (-1/4) 1, slabPt (-1/2) (-1/4) 1],
    ![slabPt (-3/4) (-1/4) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-3/4) (-1/4) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-3/4) (-1/4) 1, slabPt (-3/4) (0) 1],
    ![slabPt (-3/4) (-1/4) 1, slabPt (0) (0) 0],
    ![slabPt (-3/4) (-3/4) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-3/4) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-3/4) (-3/4) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-3/4) (-3/4) 1, slabPt (0) (0) 0],
    ![slabPt (-3/4) (0) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-3/4) (0) 1, slabPt (-3/4) (1/4) 1],
    ![slabPt (-3/4) (0) 1, slabPt (0) (0) 0],
    ![slabPt (-3/4) (1/4) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1],
    ![slabPt (-3/4) (1/4) 1, slabPt (-3/4) (0) 1],
    ![slabPt (0) (-1/4) 1, slabPt (0) (-1/2) 1],
    ![slabPt (0) (-1/4) 1, slabPt (0) (0) 1],
    ![slabPt (0) (-3/4) 1, slabPt (0) (-1/2) 1],
    ![slabPt (0) (-3/4) 1, slabPt (0) (0) 0],
    ![slabPt (0) (-3/4) 1, slabPt (1/4) (-3/4) 1],
    ![slabPt (0) (0) 0, slabPt (-3/4) (-3/4) 1],
    ![slabPt (0) (0) 0, slabPt (-3/4) (1/4) 1],
    ![slabPt (0) (0) 0, slabPt (0) (1) 0],
    ![slabPt (0) (0) 0, slabPt (1) (0) 0],
    ![slabPt (0) (0) 0, slabPt (1) (1) 0],
    ![slabPt (0) (0) 0, slabPt (1/4) (-3/4) 1],
    ![slabPt (0) (1) 0, slabPt (-3/4) (1/4) 1],
    ![slabPt (0) (1) 0, slabPt (1) (1) 0],
    ![slabPt (0) (1) 0, slabPt (1/4) (1/4) 1],
    ![slabPt (0) (1/4) 1, slabPt (0) (0) 1],
    ![slabPt (0) (1/4) 1, slabPt (0) (1) 0],
    ![slabPt (0) (1/4) 1, slabPt (1/4) (1/4) 1],
    ![slabPt (1) (0) 0, slabPt (1) (1) 0],
    ![slabPt (1) (0) 0, slabPt (1/4) (-3/4) 1],
    ![slabPt (1) (0) 0, slabPt (1/4) (1/4) 1],
    ![slabPt (1) (1) 0, slabPt (1/4) (1/4) 1],
    ![slabPt (1/2) (-1/2) 1, slabPt (1/4) (-1/2) 1],
    ![slabPt (1/2) (-1/2) 1, slabPt (1/4) (-1/4) 1],
    ![slabPt (1/2) (-1/2) 1, slabPt (1/4) (-3/4) 1],
    ![slabPt (1/2) (-3/4) 1, slabPt (1) (0) 0],
    ![slabPt (1/2) (-3/4) 1, slabPt (1/4) (-3/4) 1],
    ![slabPt (1/2) (0) 1, slabPt (1/4) (0) 1],
    ![slabPt (1/2) (0) 1, slabPt (1/4) (1/4) 1],
    ![slabPt (1/4) (-1/2) 1, slabPt (0) (-1/2) 1],
    ![slabPt (1/4) (-1/2) 1, slabPt (1) (0) 0],
    ![slabPt (1/4) (-1/2) 1, slabPt (1/4) (-1/4) 1],
    ![slabPt (1/4) (-1/2) 1, slabPt (1/4) (-3/4) 1],
    ![slabPt (1/4) (-1/4) 1, slabPt (0) (-1/2) 1],
    ![slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1],
    ![slabPt (1/4) (-1/4) 1, slabPt (0) (0) 1],
    ![slabPt (1/4) (-1/4) 1, slabPt (1) (0) 0],
    ![slabPt (1/4) (-1/4) 1, slabPt (1/4) (-1/2) 1],
    ![slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1],
    ![slabPt (1/4) (-3/4) 1, slabPt (0) (-1/2) 1],
    ![slabPt (1/4) (-3/4) 1, slabPt (0) (-3/4) 1],
    ![slabPt (1/4) (-3/4) 1, slabPt (1) (0) 0],
    ![slabPt (1/4) (-3/4) 1, slabPt (1/4) (-1/2) 1],
    ![slabPt (1/4) (0) 1, slabPt (0) (0) 1],
    ![slabPt (1/4) (0) 1, slabPt (1) (0) 0],
    ![slabPt (1/4) (0) 1, slabPt (1/4) (1/4) 1],
    ![slabPt (1/4) (1/4) 1, slabPt (0) (0) 1],
    ![slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1],
    ![slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1]]

/-- The flat index of a `(j,i)` slot. -/
def fl2 (p : Fin 24 × Fin 3) : Fin (3 * 24) :=
  ⟨3 * (p.1 : ℕ) + (p.2 : ℕ), by have h := p.1.isLt; have h2 := p.2.isLt; omega⟩
/-- The flat index of a `(j,i)` slot of the wall. -/
def flw2 (p : Fin 32 × Fin 3) : Fin (3 * 32) :=
  ⟨3 * (p.1 : ℕ) + (p.2 : ℕ), by have h := p.1.isLt; have h2 := p.2.isLt; omega⟩

def aCF2 : Fin (3 * 24) → Fin Nat2 := ![8, 1, 0, 9, 4, 0, 31, 0, 1, 47, 3, 2, 48, 4, 2, 53, 2, 3, 57, 0, 4, 58, 2, 4, 35, 10, 8, 59, 10, 9, 71, 9, 10, 71, 9, 10, 61, 12, 11, 65, 11, 12, 69, 35, 34, 70, 36, 34, 105, 34, 36, 55, 49, 47, 59, 49, 48, 62, 55, 54, 72, 61, 62, 76, 70, 69, 77, 72, 73, 84, 76, 74]
def aCF2' : Fin (3 * 24) → Fin Nat2 := ![17, 14, 13, 18, 15, 13, 40, 13, 14, 96, 88, 87, 97, 89, 87, 102, 87, 88, 64, 13, 15, 107, 87, 89, 43, 19, 17, 106, 90, 91, 84, 91, 90, 77, 18, 19, 110, 93, 92, 113, 92, 93, 81, 43, 44, 82, 45, 44, 112, 44, 45, 101, 95, 96, 106, 95, 97, 109, 101, 103, 85, 110, 109, 79, 82, 81, 86, 85, 83, 86, 79, 78]
def aWF2 : Fin (3 * 32) → Fin Nat2 := ![80, 42, 44, 80, 111, 112, 67, 29, 28, 67, 100, 99, 108, 100, 103, 108, 111, 113, 38, 29, 26, 38, 42, 41, 68, 33, 34, 68, 104, 105, 66, 27, 28, 66, 98, 99, 94, 98, 102, 94, 104, 107, 21, 27, 25, 21, 33, 32, 6, 52, 51, 6, 24, 23, 16, 63, 64, 16, 39, 40, 37, 39, 41, 37, 24, 26, 60, 63, 65, 60, 52, 54, 5, 50, 51, 5, 22, 23, 7, 56, 57, 7, 30, 31, 20, 30, 32, 20, 22, 25, 46, 56, 58, 46, 50, 53]
def aB20 : Fin 3 → Fin Nat2 := ![83, 75, 74]
def aB21 : Fin 3 → Fin Nat2 := ![78, 75, 73]

/-- The atom of the first edge family of the collar. -/
def aC2 : Fin 24 × Fin 3 → Fin Nat2 := fun p => aCF2 (fl2 p)
/-- The atom of the second edge family of the collar. -/
def aC2' : Fin 24 × Fin 3 → Fin Nat2 := fun p => aCF2' (fl2 p)
/-- The atom of the edges of the wall. -/
def aW2 : Fin 32 × Fin 3 → Fin Nat2 := fun p => aWF2 (flw2 p)

def cC2 : Fin 24 × Fin 3 → ℤ := fun p => colCoef2 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cC2' : Fin 24 × Fin 3 → ℤ := fun p => colCoef2 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cW2 : Fin 32 × Fin 3 → ℤ := fun p => coefV2 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cB2 : Fin 3 → ℤ := fun i => ((-1 : ℤ) ^ (i : ℕ))

def D12 : Fin Nat2 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aC2 p = l), cC2 p
def D22 : Fin Nat2 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aC2' p = l), cC2' p
def D32 : Fin Nat2 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aW2 p = l), cW2 p
def D42 : Fin Nat2 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aB20 p = l), cB2 p
def D52 : Fin Nat2 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aB21 p = l), cB2 p

/-- The canonical basis vector of each atom. -/
abbrev X2 : Fin Nat2 → AffC 1 := fun l => Finsupp.single (B2 l) (1 : ℤ)

set_option maxHeartbeats 0 in
/-- The pointwise coefficient identity of the collar of cusp `2`. -/
theorem hcoef2 : ∀ l : Fin Nat2, D12 l - D22 l = D32 l - (D42 l - D52 l) := by
  decide

/-- The atoms of the first edge family of the collar. -/
theorem brC2 : ∀ p : Fin 24 × Fin 3, B2 (aC2 p) = vface (k := 1) p.2 (colTri2 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j <;> fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

theorem cS2_0 : (fun k => colTri2 0 k + colLam2 0) = ![slabPt (-1/2) (1/2) (1), slabPt (-1/2) (1/4) (1), slabPt (-1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_1 : (fun k => colTri2 1 k + colLam2 1) = ![slabPt (-1/2) (1/2) (1), slabPt (-1/2) (1/4) (1), slabPt (-3/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_2 : (fun k => colTri2 2 k + colLam2 2) = ![slabPt (-1/2) (1/2) (1), slabPt (-1/4) (1/4) (1), slabPt (-1/2) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_3 : (fun k => colTri2 3 k + colLam2 3) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-1/2) (1), slabPt (1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_4 : (fun k => colTri2 4 k + colLam2 4) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-1/2) (1), slabPt (1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_5 : (fun k => colTri2 5 k + colLam2 5) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-1/4) (1), slabPt (1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem cS2_6 : (fun k => colTri2 6 k + colLam2 6) = ![slabPt (-1/2) (1/2) (1), slabPt (-3/4) (1/4) (1), slabPt (-1/2) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_7 : (fun k => colTri2 7 k + colLam2 7) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-3/4) (1), slabPt (1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem cS2_8 : (fun k => colTri2 8 k + colLam2 8) = ![slabPt (-1/2) (1/4) (1), slabPt (-1/4) (1/4) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS2_9 : (fun k => colTri2 9 k + colLam2 9) = ![slabPt (1/2) (-3/4) (1), slabPt (1/4) (-3/4) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS2_10 : (fun k => colTri2 10 k + colLam2 10) = ![slabPt (1/2) (-3/4) (1), slabPt (1) (0) (0), slabPt (1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_11 : (fun k => colTri2 11 k + colLam2 11) = ![slabPt (-1/2) (1/4) (1), slabPt (0) (1) (0), slabPt (-3/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_12 : (fun k => colTri2 12 k + colLam2 12) = ![slabPt (1/2) (0) (1), slabPt (1/4) (0) (1), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (0) (1) + slabPt (1) (0) (0) = slabPt (1/2) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_13 : (fun k => colTri2 13 k + colLam2 13) = ![slabPt (1/2) (0) (1), slabPt (1/4) (1/4) (1), slabPt (1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (0) (1) + slabPt (1) (0) (0) = slabPt (1/2) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem cS2_14 : (fun k => colTri2 14 k + colLam2 14) = ![slabPt (-1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS2_15 : (fun k => colTri2 15 k + colLam2 15) = ![slabPt (-1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_16 : (fun k => colTri2 16 k + colLam2 16) = ![slabPt (-1/4) (1/4) (1), slabPt (1/4) (1/4) (1), slabPt (0) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_17 : (fun k => colTri2 17 k + colLam2 17) = ![slabPt (1/4) (-1/2) (1), slabPt (1/4) (-1/4) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS2_18 : (fun k => colTri2 18 k + colLam2 18) = ![slabPt (1/4) (-1/2) (1), slabPt (1/4) (-3/4) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS2_19 : (fun k => colTri2 19 k + colLam2 19) = ![slabPt (1/4) (-1/4) (1), slabPt (1/4) (0) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS2_20 : (fun k => colTri2 20 k + colLam2 20) = ![slabPt (1/4) (0) (1), slabPt (1) (0) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_21 : (fun k => colTri2 21 k + colLam2 21) = ![slabPt (0) (1/4) (1), slabPt (0) (1) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_22 : (fun k => colTri2 22 k + colLam2 22) = ![slabPt (1) (0) (0), slabPt (1) (1) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1) (0) + slabPt (1) (0) (0) = slabPt (1) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS2_23 : (fun k => colTri2 23 k + colLam2 23) = ![slabPt (0) (1) (0), slabPt (1) (1) (0), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1) (0) (0) + slabPt (0) (1) (0) = slabPt (1) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS2_0 : (fun k => tauV2 0 k + lamV2 0) = ![slabPt (-1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_1 : (fun k => tauV2 1 k + lamV2 1) = ![slabPt (1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_2 : (fun k => tauV2 2 k + lamV2 2) = ![slabPt (-1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_3 : (fun k => tauV2 3 k + lamV2 3) = ![slabPt (1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_4 : (fun k => tauV2 4 k + lamV2 4) = ![slabPt (1/4) (-1/4) (1), slabPt (1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_5 : (fun k => tauV2 5 k + lamV2 5) = ![slabPt (1/4) (1/4) (1), slabPt (1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_6 : (fun k => tauV2 6 k + lamV2 6) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_7 : (fun k => tauV2 7 k + lamV2 7) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/4) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_8 : (fun k => tauV2 8 k + lamV2 8) = ![slabPt (-1/4) (-3/4) (1), slabPt (0) (-3/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_9 : (fun k => tauV2 9 k + lamV2 9) = ![slabPt (1/4) (-3/4) (1), slabPt (0) (-3/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_10 : (fun k => tauV2 10 k + lamV2 10) = ![slabPt (-1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_11 : (fun k => tauV2 11 k + lamV2 11) = ![slabPt (1/4) (-1/4) (1), slabPt (0) (-1/4) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_12 : (fun k => tauV2 12 k + lamV2 12) = ![slabPt (1/4) (-1/4) (1), slabPt (1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_13 : (fun k => tauV2 13 k + lamV2 13) = ![slabPt (1/4) (-3/4) (1), slabPt (1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_14 : (fun k => tauV2 14 k + lamV2 14) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_15 : (fun k => tauV2 15 k + lamV2 15) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_16 : (fun k => tauV2 16 k + lamV2 16) = ![slabPt (-3/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_17 : (fun k => tauV2 17 k + lamV2 17) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_18 : (fun k => tauV2 18 k + lamV2 18) = ![slabPt (-3/4) (1/4) (1), slabPt (-1/2) (1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_19 : (fun k => tauV2 19 k + lamV2 19) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/2) (1/4) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_20 : (fun k => tauV2 20 k + lamV2 20) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_21 : (fun k => tauV2 21 k + lamV2 21) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_22 : (fun k => tauV2 22 k + lamV2 22) = ![slabPt (-3/4) (1/4) (1), slabPt (-3/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_23 : (fun k => tauV2 23 k + lamV2 23) = ![slabPt (-3/4) (-1/4) (1), slabPt (-3/4) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS2_24 : (fun k => tauV2 24 k + lamV2 24) = ![slabPt (-3/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (3/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (3/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_25 : (fun k => tauV2 25 k + lamV2 25) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/2) (-1/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (3/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (3/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_26 : (fun k => tauV2 26 k + lamV2 26) = ![slabPt (-3/4) (-3/4) (1), slabPt (-1/2) (-3/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_27 : (fun k => tauV2 27 k + lamV2 27) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/2) (-3/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_28 : (fun k => tauV2 28 k + lamV2 28) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_29 : (fun k => tauV2 29 k + lamV2 29) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/4) (3/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_30 : (fun k => tauV2 30 k + lamV2 30) = ![slabPt (-3/4) (-3/4) (1), slabPt (-3/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS2_31 : (fun k => tauV2 31 k + lamV2 31) = ![slabPt (-3/4) (-1/4) (1), slabPt (-3/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/4) (3/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem brC2'_0 (i : Fin 3) : B2 (aC2' (0, i)) = vface (k := 1) i (fun k => colTri2 0 k + colLam2 0) := by
  rw [cS2_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_1 (i : Fin 3) : B2 (aC2' (1, i)) = vface (k := 1) i (fun k => colTri2 1 k + colLam2 1) := by
  rw [cS2_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_2 (i : Fin 3) : B2 (aC2' (2, i)) = vface (k := 1) i (fun k => colTri2 2 k + colLam2 2) := by
  rw [cS2_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_3 (i : Fin 3) : B2 (aC2' (3, i)) = vface (k := 1) i (fun k => colTri2 3 k + colLam2 3) := by
  rw [cS2_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_4 (i : Fin 3) : B2 (aC2' (4, i)) = vface (k := 1) i (fun k => colTri2 4 k + colLam2 4) := by
  rw [cS2_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_5 (i : Fin 3) : B2 (aC2' (5, i)) = vface (k := 1) i (fun k => colTri2 5 k + colLam2 5) := by
  rw [cS2_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_6 (i : Fin 3) : B2 (aC2' (6, i)) = vface (k := 1) i (fun k => colTri2 6 k + colLam2 6) := by
  rw [cS2_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_7 (i : Fin 3) : B2 (aC2' (7, i)) = vface (k := 1) i (fun k => colTri2 7 k + colLam2 7) := by
  rw [cS2_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_8 (i : Fin 3) : B2 (aC2' (8, i)) = vface (k := 1) i (fun k => colTri2 8 k + colLam2 8) := by
  rw [cS2_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_9 (i : Fin 3) : B2 (aC2' (9, i)) = vface (k := 1) i (fun k => colTri2 9 k + colLam2 9) := by
  rw [cS2_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_10 (i : Fin 3) : B2 (aC2' (10, i)) = vface (k := 1) i (fun k => colTri2 10 k + colLam2 10) := by
  rw [cS2_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_11 (i : Fin 3) : B2 (aC2' (11, i)) = vface (k := 1) i (fun k => colTri2 11 k + colLam2 11) := by
  rw [cS2_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_12 (i : Fin 3) : B2 (aC2' (12, i)) = vface (k := 1) i (fun k => colTri2 12 k + colLam2 12) := by
  rw [cS2_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_13 (i : Fin 3) : B2 (aC2' (13, i)) = vface (k := 1) i (fun k => colTri2 13 k + colLam2 13) := by
  rw [cS2_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_14 (i : Fin 3) : B2 (aC2' (14, i)) = vface (k := 1) i (fun k => colTri2 14 k + colLam2 14) := by
  rw [cS2_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_15 (i : Fin 3) : B2 (aC2' (15, i)) = vface (k := 1) i (fun k => colTri2 15 k + colLam2 15) := by
  rw [cS2_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_16 (i : Fin 3) : B2 (aC2' (16, i)) = vface (k := 1) i (fun k => colTri2 16 k + colLam2 16) := by
  rw [cS2_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_17 (i : Fin 3) : B2 (aC2' (17, i)) = vface (k := 1) i (fun k => colTri2 17 k + colLam2 17) := by
  rw [cS2_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_18 (i : Fin 3) : B2 (aC2' (18, i)) = vface (k := 1) i (fun k => colTri2 18 k + colLam2 18) := by
  rw [cS2_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_19 (i : Fin 3) : B2 (aC2' (19, i)) = vface (k := 1) i (fun k => colTri2 19 k + colLam2 19) := by
  rw [cS2_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_20 (i : Fin 3) : B2 (aC2' (20, i)) = vface (k := 1) i (fun k => colTri2 20 k + colLam2 20) := by
  rw [cS2_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_21 (i : Fin 3) : B2 (aC2' (21, i)) = vface (k := 1) i (fun k => colTri2 21 k + colLam2 21) := by
  rw [cS2_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_22 (i : Fin 3) : B2 (aC2' (22, i)) = vface (k := 1) i (fun k => colTri2 22 k + colLam2 22) := by
  rw [cS2_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC2'_23 (i : Fin 3) : B2 (aC2' (23, i)) = vface (k := 1) i (fun k => colTri2 23 k + colLam2 23) := by
  rw [cS2_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_0 (i : Fin 3) : B2 (aW2 (0, i)) = vface (k := 1) i (fun k => tauV2 0 k + lamV2 0) := by
  rw [tS2_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_1 (i : Fin 3) : B2 (aW2 (1, i)) = vface (k := 1) i (fun k => tauV2 1 k + lamV2 1) := by
  rw [tS2_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_2 (i : Fin 3) : B2 (aW2 (2, i)) = vface (k := 1) i (fun k => tauV2 2 k + lamV2 2) := by
  rw [tS2_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_3 (i : Fin 3) : B2 (aW2 (3, i)) = vface (k := 1) i (fun k => tauV2 3 k + lamV2 3) := by
  rw [tS2_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_4 (i : Fin 3) : B2 (aW2 (4, i)) = vface (k := 1) i (fun k => tauV2 4 k + lamV2 4) := by
  rw [tS2_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_5 (i : Fin 3) : B2 (aW2 (5, i)) = vface (k := 1) i (fun k => tauV2 5 k + lamV2 5) := by
  rw [tS2_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_6 (i : Fin 3) : B2 (aW2 (6, i)) = vface (k := 1) i (fun k => tauV2 6 k + lamV2 6) := by
  rw [tS2_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_7 (i : Fin 3) : B2 (aW2 (7, i)) = vface (k := 1) i (fun k => tauV2 7 k + lamV2 7) := by
  rw [tS2_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_8 (i : Fin 3) : B2 (aW2 (8, i)) = vface (k := 1) i (fun k => tauV2 8 k + lamV2 8) := by
  rw [tS2_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_9 (i : Fin 3) : B2 (aW2 (9, i)) = vface (k := 1) i (fun k => tauV2 9 k + lamV2 9) := by
  rw [tS2_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_10 (i : Fin 3) : B2 (aW2 (10, i)) = vface (k := 1) i (fun k => tauV2 10 k + lamV2 10) := by
  rw [tS2_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_11 (i : Fin 3) : B2 (aW2 (11, i)) = vface (k := 1) i (fun k => tauV2 11 k + lamV2 11) := by
  rw [tS2_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_12 (i : Fin 3) : B2 (aW2 (12, i)) = vface (k := 1) i (fun k => tauV2 12 k + lamV2 12) := by
  rw [tS2_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_13 (i : Fin 3) : B2 (aW2 (13, i)) = vface (k := 1) i (fun k => tauV2 13 k + lamV2 13) := by
  rw [tS2_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_14 (i : Fin 3) : B2 (aW2 (14, i)) = vface (k := 1) i (fun k => tauV2 14 k + lamV2 14) := by
  rw [tS2_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_15 (i : Fin 3) : B2 (aW2 (15, i)) = vface (k := 1) i (fun k => tauV2 15 k + lamV2 15) := by
  rw [tS2_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_16 (i : Fin 3) : B2 (aW2 (16, i)) = vface (k := 1) i (fun k => tauV2 16 k + lamV2 16) := by
  rw [tS2_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_17 (i : Fin 3) : B2 (aW2 (17, i)) = vface (k := 1) i (fun k => tauV2 17 k + lamV2 17) := by
  rw [tS2_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_18 (i : Fin 3) : B2 (aW2 (18, i)) = vface (k := 1) i (fun k => tauV2 18 k + lamV2 18) := by
  rw [tS2_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_19 (i : Fin 3) : B2 (aW2 (19, i)) = vface (k := 1) i (fun k => tauV2 19 k + lamV2 19) := by
  rw [tS2_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_20 (i : Fin 3) : B2 (aW2 (20, i)) = vface (k := 1) i (fun k => tauV2 20 k + lamV2 20) := by
  rw [tS2_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_21 (i : Fin 3) : B2 (aW2 (21, i)) = vface (k := 1) i (fun k => tauV2 21 k + lamV2 21) := by
  rw [tS2_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_22 (i : Fin 3) : B2 (aW2 (22, i)) = vface (k := 1) i (fun k => tauV2 22 k + lamV2 22) := by
  rw [tS2_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_23 (i : Fin 3) : B2 (aW2 (23, i)) = vface (k := 1) i (fun k => tauV2 23 k + lamV2 23) := by
  rw [tS2_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_24 (i : Fin 3) : B2 (aW2 (24, i)) = vface (k := 1) i (fun k => tauV2 24 k + lamV2 24) := by
  rw [tS2_24]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_25 (i : Fin 3) : B2 (aW2 (25, i)) = vface (k := 1) i (fun k => tauV2 25 k + lamV2 25) := by
  rw [tS2_25]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_26 (i : Fin 3) : B2 (aW2 (26, i)) = vface (k := 1) i (fun k => tauV2 26 k + lamV2 26) := by
  rw [tS2_26]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_27 (i : Fin 3) : B2 (aW2 (27, i)) = vface (k := 1) i (fun k => tauV2 27 k + lamV2 27) := by
  rw [tS2_27]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_28 (i : Fin 3) : B2 (aW2 (28, i)) = vface (k := 1) i (fun k => tauV2 28 k + lamV2 28) := by
  rw [tS2_28]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_29 (i : Fin 3) : B2 (aW2 (29, i)) = vface (k := 1) i (fun k => tauV2 29 k + lamV2 29) := by
  rw [tS2_29]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_30 (i : Fin 3) : B2 (aW2 (30, i)) = vface (k := 1) i (fun k => tauV2 30 k + lamV2 30) := by
  rw [tS2_30]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW2_31 (i : Fin 3) : B2 (aW2 (31, i)) = vface (k := 1) i (fun k => tauV2 31 k + lamV2 31) := by
  rw [tS2_31]; fin_cases i <;> funext k <;> fin_cases k <;> rfl

/-- The atoms of the second edge family of the collar. -/
theorem brC2' : ∀ p : Fin 24 × Fin 3,
    B2 (aC2' p) = vface (k := 1) p.2 (fun k => colTri2 p.1 k + colLam2 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brC2'_0 i, brC2'_1 i, brC2'_2 i, brC2'_3 i, brC2'_4 i, brC2'_5 i, brC2'_6 i, brC2'_7 i, brC2'_8 i, brC2'_9 i, brC2'_10 i, brC2'_11 i, brC2'_12 i, brC2'_13 i, brC2'_14 i, brC2'_15 i, brC2'_16 i, brC2'_17 i, brC2'_18 i, brC2'_19 i, brC2'_20 i, brC2'_21 i, brC2'_22 i, brC2'_23 i]

/-- The atoms of the edges of the wall. -/
theorem brW2 : ∀ p : Fin 32 × Fin 3,
    B2 (aW2 p) = vface (k := 1) p.2 (fun k => tauV2 p.1 k + lamV2 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brW2_0 i, brW2_1 i, brW2_2 i, brW2_3 i, brW2_4 i, brW2_5 i, brW2_6 i, brW2_7 i, brW2_8 i, brW2_9 i, brW2_10 i, brW2_11 i, brW2_12 i, brW2_13 i, brW2_14 i, brW2_15 i, brW2_16 i, brW2_17 i, brW2_18 i, brW2_19 i, brW2_20 i, brW2_21 i, brW2_22 i, brW2_23 i, brW2_24 i, brW2_25 i, brW2_26 i, brW2_27 i, brW2_28 i, brW2_29 i, brW2_30 i, brW2_31 i]

/-- The atoms of the first coarse triangle. -/
theorem brB20 : ∀ i : Fin 3, B2 (aB20 i) = vface (k := 1) i botV0 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

/-- The atoms of the second coarse triangle. -/
theorem brB21 : ∀ i : Fin 3, B2 (aB21 i) = vface (k := 1) i botV1 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

theorem colLam_mem2 (j : NCol2) : slabL 2 (colLam2 j) ∈ Work.Cusp.lattice 2 := by
  have h : slabL 2 (colLam2 j) ∈ ({Work.Cusp.kv 2 1, Work.Cusp.kv 2 2} : Set CuspE3) := by
    fin_cases j <;> simp [colLam2, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3]
  rcases h with h | h
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 1)
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 2)

/-- **The collar of cusp `2` is in the kernel of `slabChain`.** -/
theorem collar_slab2 : slabChain 2 2 (collarChain2 : AffC 2) = 0 := by
  rw [collarChain2, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, map_sub, slabChain_single_one, slabChain_single_one]
  have h1 : slabV 2 (fun k => colTri2 j k + colLam2 j)
      = fun k => slabV 2 (colTri2 j) k + slabL 2 (colLam2 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 2 (slabV 2 (colTri2 j)) (slabL 2 (colLam2 j))
        (colLam_mem2 j), sub_self, smul_zero]

/-- **The boundary of the collar of cusp `2`.** -/
theorem dLC_collar2 :
    dLC 1 (collarChain2 : AffC 2) = dLC 1 (wallChain2 : AffC 2) - dLC 1 slabBot := by
  have hP1 : (∑ j : NCol2, dLC 1 (colCoef2 j • Finsupp.single (colTri2 j) (1 : ℤ)))
      = ∑ p : Fin 24 × Fin 3, cC2 p • X2 (aC2 p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC2, ← smul_smul, ← brC2 (j, i)]
  have hP2 : (∑ j : NCol2, dLC 1 (colCoef2 j •
        Finsupp.single (fun k => colTri2 j k + colLam2 j) (1 : ℤ)))
      = ∑ p : Fin 24 × Fin 3, cC2' p • X2 (aC2' p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC2', ← smul_smul, ← brC2' (j, i)]
  have hQ1 : (∑ p : Fin 24 × Fin 3, cC2 p • X2 (aC2 p))
      = ∑ l : Fin Nat2, D12 l • X2 l :=
    sum_smul_regroup aC2 cC2 X2
  have hQ2 : (∑ p : Fin 24 × Fin 3, cC2' p • X2 (aC2' p))
      = ∑ l : Fin Nat2, D22 l • X2 l :=
    sum_smul_regroup aC2' cC2' X2
  have hW : (∑ p : Fin 32 × Fin 3, cW2 p • X2 (aW2 p))
      = ∑ l : Fin Nat2, D32 l • X2 l :=
    sum_smul_regroup aW2 cW2 X2
  have hB0 : (∑ i : Fin 3, cB2 i • X2 (aB20 i))
      = ∑ l : Fin Nat2, D42 l • X2 l :=
    sum_smul_regroup aB20 cB2 X2
  have hB1 : (∑ i : Fin 3, cB2 i • X2 (aB21 i))
      = ∑ l : Fin Nat2, D52 l • X2 l :=
    sum_smul_regroup aB21 cB2 X2
  have hwall : dLC 1 (wallChain2 : AffC 2)
      = ∑ p : Fin 32 × Fin 3, cW2 p • X2 (aW2 p) := by
    rw [wallChain2, map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cW2, ← smul_smul, ← brW2 (j, i)]
  have hbot : dLC 1 slabBot
      = (∑ i : Fin 3, cB2 i • X2 (aB20 i))
        - (∑ i : Fin 3, cB2 i • X2 (aB21 i)) := by
    rw [slabBot, map_sub, dLC_single, dLC_single]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB2, ← brB20 i]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB2, ← brB21 i]
  have hcol : dLC 1 (collarChain2 : AffC 2)
      = (∑ j : NCol2, dLC 1 (colCoef2 j • Finsupp.single (colTri2 j) (1 : ℤ)))
        - (∑ j : NCol2, dLC 1 (colCoef2 j •
            Finsupp.single (fun k => colTri2 j k + colLam2 j) (1 : ℤ))) := by
    rw [collarChain2, map_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_sub, smul_sub, map_smul, map_smul]
  have hcoef : ∀ l : Fin Nat2, D12 l - D22 l = D32 l - (D42 l - D52 l) := hcoef2
  rw [hcol, hP1, hP2, hQ1, hQ2, hwall, hW, hbot, hB0, hB1]
  exact sum_smul_four D12 D22 D32 D42 D52 X2 hcoef

end

end Work.BridgeSquare.SlabBuild

