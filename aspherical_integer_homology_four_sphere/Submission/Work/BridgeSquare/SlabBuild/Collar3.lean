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

/-! ## The collar identity of cusp `3`

`D1`..`D5`  are the coefficient tables of the five pieces of the identity
`dLC 1 collarChain3 = dLC 1 wallChain3 - dLC 1 slabBot`, indexed by the *atoms* (the
directed edges) `B3`, and `aC3`..`aB31` are the atom of each slot of each piece.  The
identity is then the pointwise identity of the coefficients `D1 - D2 = D3 - (D4 - D5)`.
-/

/-- The number of distinct atoms of the collar identity of cusp `3`. -/
abbrev Nat3 : ℕ := 114
/-- The atoms (directed edges) of the collar identity of cusp `3`. -/
def B3 : Fin Nat3 → (Fin 2 → CuspE3) :=
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
def fl3 (p : Fin 24 × Fin 3) : Fin (3 * 24) :=
  ⟨3 * (p.1 : ℕ) + (p.2 : ℕ), by have h := p.1.isLt; have h2 := p.2.isLt; omega⟩
/-- The flat index of a `(j,i)` slot of the wall. -/
def flw3 (p : Fin 32 × Fin 3) : Fin (3 * 32) :=
  ⟨3 * (p.1 : ℕ) + (p.2 : ℕ), by have h := p.1.isLt; have h2 := p.2.isLt; omega⟩

def aCF3 : Fin (3 * 24) → Fin Nat3 := ![8, 1, 0, 9, 4, 0, 31, 0, 1, 47, 3, 2, 48, 4, 2, 53, 2, 3, 57, 0, 4, 58, 2, 4, 35, 10, 8, 59, 10, 9, 71, 9, 10, 71, 9, 10, 61, 12, 11, 65, 11, 12, 69, 35, 34, 70, 36, 34, 105, 34, 36, 55, 49, 47, 59, 49, 48, 62, 55, 54, 72, 61, 62, 76, 70, 69, 77, 72, 73, 84, 76, 74]
def aCF3' : Fin (3 * 24) → Fin Nat3 := ![17, 14, 13, 18, 15, 13, 40, 13, 14, 96, 88, 87, 97, 89, 87, 102, 87, 88, 64, 13, 15, 107, 87, 89, 43, 19, 17, 106, 90, 91, 84, 91, 90, 77, 18, 19, 110, 93, 92, 113, 92, 93, 81, 43, 44, 82, 45, 44, 112, 44, 45, 101, 95, 96, 106, 95, 97, 109, 101, 103, 85, 110, 109, 79, 82, 81, 86, 85, 83, 86, 79, 78]
def aWF3 : Fin (3 * 32) → Fin Nat3 := ![80, 42, 44, 80, 111, 112, 67, 29, 28, 67, 100, 99, 108, 100, 103, 108, 111, 113, 38, 29, 26, 38, 42, 41, 66, 98, 99, 66, 27, 28, 68, 104, 105, 68, 33, 34, 21, 33, 32, 21, 27, 25, 94, 104, 107, 94, 98, 102, 16, 39, 40, 16, 63, 64, 6, 24, 23, 6, 52, 51, 60, 52, 54, 60, 63, 65, 37, 24, 26, 37, 39, 41, 5, 50, 51, 5, 22, 23, 7, 56, 57, 7, 30, 31, 20, 30, 32, 20, 22, 25, 46, 56, 58, 46, 50, 53]
def aB30 : Fin 3 → Fin Nat3 := ![83, 75, 74]
def aB31 : Fin 3 → Fin Nat3 := ![78, 75, 73]

/-- The atom of the first edge family of the collar. -/
def aC3 : Fin 24 × Fin 3 → Fin Nat3 := fun p => aCF3 (fl3 p)
/-- The atom of the second edge family of the collar. -/
def aC3' : Fin 24 × Fin 3 → Fin Nat3 := fun p => aCF3' (fl3 p)
/-- The atom of the edges of the wall. -/
def aW3 : Fin 32 × Fin 3 → Fin Nat3 := fun p => aWF3 (flw3 p)

def cC3 : Fin 24 × Fin 3 → ℤ := fun p => colCoef3 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cC3' : Fin 24 × Fin 3 → ℤ := fun p => colCoef3 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cW3 : Fin 32 × Fin 3 → ℤ := fun p => coefV3 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cB3 : Fin 3 → ℤ := fun i => ((-1 : ℤ) ^ (i : ℕ))

def D13 : Fin Nat3 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aC3 p = l), cC3 p
def D23 : Fin Nat3 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aC3' p = l), cC3' p
def D33 : Fin Nat3 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aW3 p = l), cW3 p
def D43 : Fin Nat3 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aB30 p = l), cB3 p
def D53 : Fin Nat3 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aB31 p = l), cB3 p

/-- The canonical basis vector of each atom. -/
abbrev X3 : Fin Nat3 → AffC 1 := fun l => Finsupp.single (B3 l) (1 : ℤ)

set_option maxHeartbeats 0 in
/-- The pointwise coefficient identity of the collar of cusp `3`. -/
theorem hcoef3 : ∀ l : Fin Nat3, D13 l - D23 l = D33 l - (D43 l - D53 l) := by
  decide

/-- The atoms of the first edge family of the collar. -/
theorem brC3 : ∀ p : Fin 24 × Fin 3, B3 (aC3 p) = vface (k := 1) p.2 (colTri3 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j <;> fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

theorem cS3_0 : (fun k => colTri3 0 k + colLam3 0) = ![slabPt (-1/2) (1/2) (1), slabPt (-1/2) (1/4) (1), slabPt (-1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_1 : (fun k => colTri3 1 k + colLam3 1) = ![slabPt (-1/2) (1/2) (1), slabPt (-1/2) (1/4) (1), slabPt (-3/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_2 : (fun k => colTri3 2 k + colLam3 2) = ![slabPt (-1/2) (1/2) (1), slabPt (-1/4) (1/4) (1), slabPt (-1/2) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_3 : (fun k => colTri3 3 k + colLam3 3) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-1/2) (1), slabPt (1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_4 : (fun k => colTri3 4 k + colLam3 4) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-1/2) (1), slabPt (1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_5 : (fun k => colTri3 5 k + colLam3 5) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-1/4) (1), slabPt (1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem cS3_6 : (fun k => colTri3 6 k + colLam3 6) = ![slabPt (-1/2) (1/2) (1), slabPt (-3/4) (1/4) (1), slabPt (-1/2) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_7 : (fun k => colTri3 7 k + colLam3 7) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-3/4) (1), slabPt (1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem cS3_8 : (fun k => colTri3 8 k + colLam3 8) = ![slabPt (-1/2) (1/4) (1), slabPt (-1/4) (1/4) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS3_9 : (fun k => colTri3 9 k + colLam3 9) = ![slabPt (1/2) (-3/4) (1), slabPt (1/4) (-3/4) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS3_10 : (fun k => colTri3 10 k + colLam3 10) = ![slabPt (1/2) (-3/4) (1), slabPt (1) (0) (0), slabPt (1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_11 : (fun k => colTri3 11 k + colLam3 11) = ![slabPt (-1/2) (1/4) (1), slabPt (0) (1) (0), slabPt (-3/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_12 : (fun k => colTri3 12 k + colLam3 12) = ![slabPt (1/2) (0) (1), slabPt (1/4) (0) (1), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (0) (1) + slabPt (1) (0) (0) = slabPt (1/2) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS3_13 : (fun k => colTri3 13 k + colLam3 13) = ![slabPt (1/2) (0) (1), slabPt (1/4) (1/4) (1), slabPt (1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (0) (1) + slabPt (1) (0) (0) = slabPt (1/2) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem cS3_14 : (fun k => colTri3 14 k + colLam3 14) = ![slabPt (-1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS3_15 : (fun k => colTri3 15 k + colLam3 15) = ![slabPt (-1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

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

theorem tS3_27 : (fun k => tauV3 27 k + lamV3 27) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/2) (-3/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_28 : (fun k => tauV3 28 k + lamV3 28) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_29 : (fun k => tauV3 29 k + lamV3 29) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_30 : (fun k => tauV3 30 k + lamV3 30) = ![slabPt (-3/4) (-3/4) (1), slabPt (-3/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS3_31 : (fun k => tauV3 31 k + lamV3 31) = ![slabPt (-3/4) (-1/4) (1), slabPt (-3/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem brC3'_0 (i : Fin 3) : B3 (aC3' (0, i)) = vface (k := 1) i (fun k => colTri3 0 k + colLam3 0) := by
  rw [cS3_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_1 (i : Fin 3) : B3 (aC3' (1, i)) = vface (k := 1) i (fun k => colTri3 1 k + colLam3 1) := by
  rw [cS3_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_2 (i : Fin 3) : B3 (aC3' (2, i)) = vface (k := 1) i (fun k => colTri3 2 k + colLam3 2) := by
  rw [cS3_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_3 (i : Fin 3) : B3 (aC3' (3, i)) = vface (k := 1) i (fun k => colTri3 3 k + colLam3 3) := by
  rw [cS3_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_4 (i : Fin 3) : B3 (aC3' (4, i)) = vface (k := 1) i (fun k => colTri3 4 k + colLam3 4) := by
  rw [cS3_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_5 (i : Fin 3) : B3 (aC3' (5, i)) = vface (k := 1) i (fun k => colTri3 5 k + colLam3 5) := by
  rw [cS3_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_6 (i : Fin 3) : B3 (aC3' (6, i)) = vface (k := 1) i (fun k => colTri3 6 k + colLam3 6) := by
  rw [cS3_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_7 (i : Fin 3) : B3 (aC3' (7, i)) = vface (k := 1) i (fun k => colTri3 7 k + colLam3 7) := by
  rw [cS3_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_8 (i : Fin 3) : B3 (aC3' (8, i)) = vface (k := 1) i (fun k => colTri3 8 k + colLam3 8) := by
  rw [cS3_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_9 (i : Fin 3) : B3 (aC3' (9, i)) = vface (k := 1) i (fun k => colTri3 9 k + colLam3 9) := by
  rw [cS3_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_10 (i : Fin 3) : B3 (aC3' (10, i)) = vface (k := 1) i (fun k => colTri3 10 k + colLam3 10) := by
  rw [cS3_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_11 (i : Fin 3) : B3 (aC3' (11, i)) = vface (k := 1) i (fun k => colTri3 11 k + colLam3 11) := by
  rw [cS3_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_12 (i : Fin 3) : B3 (aC3' (12, i)) = vface (k := 1) i (fun k => colTri3 12 k + colLam3 12) := by
  rw [cS3_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_13 (i : Fin 3) : B3 (aC3' (13, i)) = vface (k := 1) i (fun k => colTri3 13 k + colLam3 13) := by
  rw [cS3_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_14 (i : Fin 3) : B3 (aC3' (14, i)) = vface (k := 1) i (fun k => colTri3 14 k + colLam3 14) := by
  rw [cS3_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_15 (i : Fin 3) : B3 (aC3' (15, i)) = vface (k := 1) i (fun k => colTri3 15 k + colLam3 15) := by
  rw [cS3_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_16 (i : Fin 3) : B3 (aC3' (16, i)) = vface (k := 1) i (fun k => colTri3 16 k + colLam3 16) := by
  rw [cS3_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_17 (i : Fin 3) : B3 (aC3' (17, i)) = vface (k := 1) i (fun k => colTri3 17 k + colLam3 17) := by
  rw [cS3_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_18 (i : Fin 3) : B3 (aC3' (18, i)) = vface (k := 1) i (fun k => colTri3 18 k + colLam3 18) := by
  rw [cS3_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_19 (i : Fin 3) : B3 (aC3' (19, i)) = vface (k := 1) i (fun k => colTri3 19 k + colLam3 19) := by
  rw [cS3_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_20 (i : Fin 3) : B3 (aC3' (20, i)) = vface (k := 1) i (fun k => colTri3 20 k + colLam3 20) := by
  rw [cS3_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_21 (i : Fin 3) : B3 (aC3' (21, i)) = vface (k := 1) i (fun k => colTri3 21 k + colLam3 21) := by
  rw [cS3_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_22 (i : Fin 3) : B3 (aC3' (22, i)) = vface (k := 1) i (fun k => colTri3 22 k + colLam3 22) := by
  rw [cS3_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC3'_23 (i : Fin 3) : B3 (aC3' (23, i)) = vface (k := 1) i (fun k => colTri3 23 k + colLam3 23) := by
  rw [cS3_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_0 (i : Fin 3) : B3 (aW3 (0, i)) = vface (k := 1) i (fun k => tauV3 0 k + lamV3 0) := by
  rw [tS3_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_1 (i : Fin 3) : B3 (aW3 (1, i)) = vface (k := 1) i (fun k => tauV3 1 k + lamV3 1) := by
  rw [tS3_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_2 (i : Fin 3) : B3 (aW3 (2, i)) = vface (k := 1) i (fun k => tauV3 2 k + lamV3 2) := by
  rw [tS3_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_3 (i : Fin 3) : B3 (aW3 (3, i)) = vface (k := 1) i (fun k => tauV3 3 k + lamV3 3) := by
  rw [tS3_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_4 (i : Fin 3) : B3 (aW3 (4, i)) = vface (k := 1) i (fun k => tauV3 4 k + lamV3 4) := by
  rw [tS3_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_5 (i : Fin 3) : B3 (aW3 (5, i)) = vface (k := 1) i (fun k => tauV3 5 k + lamV3 5) := by
  rw [tS3_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_6 (i : Fin 3) : B3 (aW3 (6, i)) = vface (k := 1) i (fun k => tauV3 6 k + lamV3 6) := by
  rw [tS3_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_7 (i : Fin 3) : B3 (aW3 (7, i)) = vface (k := 1) i (fun k => tauV3 7 k + lamV3 7) := by
  rw [tS3_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_8 (i : Fin 3) : B3 (aW3 (8, i)) = vface (k := 1) i (fun k => tauV3 8 k + lamV3 8) := by
  rw [tS3_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_9 (i : Fin 3) : B3 (aW3 (9, i)) = vface (k := 1) i (fun k => tauV3 9 k + lamV3 9) := by
  rw [tS3_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_10 (i : Fin 3) : B3 (aW3 (10, i)) = vface (k := 1) i (fun k => tauV3 10 k + lamV3 10) := by
  rw [tS3_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_11 (i : Fin 3) : B3 (aW3 (11, i)) = vface (k := 1) i (fun k => tauV3 11 k + lamV3 11) := by
  rw [tS3_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_12 (i : Fin 3) : B3 (aW3 (12, i)) = vface (k := 1) i (fun k => tauV3 12 k + lamV3 12) := by
  rw [tS3_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_13 (i : Fin 3) : B3 (aW3 (13, i)) = vface (k := 1) i (fun k => tauV3 13 k + lamV3 13) := by
  rw [tS3_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_14 (i : Fin 3) : B3 (aW3 (14, i)) = vface (k := 1) i (fun k => tauV3 14 k + lamV3 14) := by
  rw [tS3_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_15 (i : Fin 3) : B3 (aW3 (15, i)) = vface (k := 1) i (fun k => tauV3 15 k + lamV3 15) := by
  rw [tS3_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_16 (i : Fin 3) : B3 (aW3 (16, i)) = vface (k := 1) i (fun k => tauV3 16 k + lamV3 16) := by
  rw [tS3_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_17 (i : Fin 3) : B3 (aW3 (17, i)) = vface (k := 1) i (fun k => tauV3 17 k + lamV3 17) := by
  rw [tS3_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_18 (i : Fin 3) : B3 (aW3 (18, i)) = vface (k := 1) i (fun k => tauV3 18 k + lamV3 18) := by
  rw [tS3_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_19 (i : Fin 3) : B3 (aW3 (19, i)) = vface (k := 1) i (fun k => tauV3 19 k + lamV3 19) := by
  rw [tS3_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_20 (i : Fin 3) : B3 (aW3 (20, i)) = vface (k := 1) i (fun k => tauV3 20 k + lamV3 20) := by
  rw [tS3_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_21 (i : Fin 3) : B3 (aW3 (21, i)) = vface (k := 1) i (fun k => tauV3 21 k + lamV3 21) := by
  rw [tS3_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_22 (i : Fin 3) : B3 (aW3 (22, i)) = vface (k := 1) i (fun k => tauV3 22 k + lamV3 22) := by
  rw [tS3_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_23 (i : Fin 3) : B3 (aW3 (23, i)) = vface (k := 1) i (fun k => tauV3 23 k + lamV3 23) := by
  rw [tS3_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_24 (i : Fin 3) : B3 (aW3 (24, i)) = vface (k := 1) i (fun k => tauV3 24 k + lamV3 24) := by
  rw [tS3_24]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_25 (i : Fin 3) : B3 (aW3 (25, i)) = vface (k := 1) i (fun k => tauV3 25 k + lamV3 25) := by
  rw [tS3_25]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_26 (i : Fin 3) : B3 (aW3 (26, i)) = vface (k := 1) i (fun k => tauV3 26 k + lamV3 26) := by
  rw [tS3_26]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_27 (i : Fin 3) : B3 (aW3 (27, i)) = vface (k := 1) i (fun k => tauV3 27 k + lamV3 27) := by
  rw [tS3_27]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_28 (i : Fin 3) : B3 (aW3 (28, i)) = vface (k := 1) i (fun k => tauV3 28 k + lamV3 28) := by
  rw [tS3_28]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_29 (i : Fin 3) : B3 (aW3 (29, i)) = vface (k := 1) i (fun k => tauV3 29 k + lamV3 29) := by
  rw [tS3_29]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_30 (i : Fin 3) : B3 (aW3 (30, i)) = vface (k := 1) i (fun k => tauV3 30 k + lamV3 30) := by
  rw [tS3_30]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW3_31 (i : Fin 3) : B3 (aW3 (31, i)) = vface (k := 1) i (fun k => tauV3 31 k + lamV3 31) := by
  rw [tS3_31]; fin_cases i <;> funext k <;> fin_cases k <;> rfl

/-- The atoms of the second edge family of the collar. -/
theorem brC3' : ∀ p : Fin 24 × Fin 3,
    B3 (aC3' p) = vface (k := 1) p.2 (fun k => colTri3 p.1 k + colLam3 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brC3'_0 i, brC3'_1 i, brC3'_2 i, brC3'_3 i, brC3'_4 i, brC3'_5 i, brC3'_6 i, brC3'_7 i, brC3'_8 i, brC3'_9 i, brC3'_10 i, brC3'_11 i, brC3'_12 i, brC3'_13 i, brC3'_14 i, brC3'_15 i, brC3'_16 i, brC3'_17 i, brC3'_18 i, brC3'_19 i, brC3'_20 i, brC3'_21 i, brC3'_22 i, brC3'_23 i]

/-- The atoms of the edges of the wall. -/
theorem brW3 : ∀ p : Fin 32 × Fin 3,
    B3 (aW3 p) = vface (k := 1) p.2 (fun k => tauV3 p.1 k + lamV3 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brW3_0 i, brW3_1 i, brW3_2 i, brW3_3 i, brW3_4 i, brW3_5 i, brW3_6 i, brW3_7 i, brW3_8 i, brW3_9 i, brW3_10 i, brW3_11 i, brW3_12 i, brW3_13 i, brW3_14 i, brW3_15 i, brW3_16 i, brW3_17 i, brW3_18 i, brW3_19 i, brW3_20 i, brW3_21 i, brW3_22 i, brW3_23 i, brW3_24 i, brW3_25 i, brW3_26 i, brW3_27 i, brW3_28 i, brW3_29 i, brW3_30 i, brW3_31 i]

/-- The atoms of the first coarse triangle. -/
theorem brB30 : ∀ i : Fin 3, B3 (aB30 i) = vface (k := 1) i botV0 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

/-- The atoms of the second coarse triangle. -/
theorem brB31 : ∀ i : Fin 3, B3 (aB31 i) = vface (k := 1) i botV1 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

theorem colLam_mem3 (j : NCol3) : slabL 3 (colLam3 j) ∈ Work.Cusp.lattice 3 := by
  have h : slabL 3 (colLam3 j) ∈ ({Work.Cusp.kv 3 1, Work.Cusp.kv 3 2} : Set CuspE3) := by
    fin_cases j <;> simp [colLam3, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3]
  rcases h with h | h
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 1)
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 2)

/-- **The collar of cusp `3` is in the kernel of `slabChain`.** -/
theorem collar_slab3 : slabChain 3 2 (collarChain3 : AffC 2) = 0 := by
  rw [collarChain3, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, map_sub, slabChain_single_one, slabChain_single_one]
  have h1 : slabV 3 (fun k => colTri3 j k + colLam3 j)
      = fun k => slabV 3 (colTri3 j) k + slabL 3 (colLam3 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 3 (slabV 3 (colTri3 j)) (slabL 3 (colLam3 j))
        (colLam_mem3 j), sub_self, smul_zero]

/-- **The boundary of the collar of cusp `3`.** -/
theorem dLC_collar3 :
    dLC 1 (collarChain3 : AffC 2) = dLC 1 (wallChain3 : AffC 2) - dLC 1 slabBot := by
  have hP1 : (∑ j : NCol3, dLC 1 (colCoef3 j • Finsupp.single (colTri3 j) (1 : ℤ)))
      = ∑ p : Fin 24 × Fin 3, cC3 p • X3 (aC3 p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC3, ← smul_smul, ← brC3 (j, i)]
  have hP2 : (∑ j : NCol3, dLC 1 (colCoef3 j •
        Finsupp.single (fun k => colTri3 j k + colLam3 j) (1 : ℤ)))
      = ∑ p : Fin 24 × Fin 3, cC3' p • X3 (aC3' p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC3', ← smul_smul, ← brC3' (j, i)]
  have hQ1 : (∑ p : Fin 24 × Fin 3, cC3 p • X3 (aC3 p))
      = ∑ l : Fin Nat3, D13 l • X3 l :=
    sum_smul_regroup aC3 cC3 X3
  have hQ2 : (∑ p : Fin 24 × Fin 3, cC3' p • X3 (aC3' p))
      = ∑ l : Fin Nat3, D23 l • X3 l :=
    sum_smul_regroup aC3' cC3' X3
  have hW : (∑ p : Fin 32 × Fin 3, cW3 p • X3 (aW3 p))
      = ∑ l : Fin Nat3, D33 l • X3 l :=
    sum_smul_regroup aW3 cW3 X3
  have hB0 : (∑ i : Fin 3, cB3 i • X3 (aB30 i))
      = ∑ l : Fin Nat3, D43 l • X3 l :=
    sum_smul_regroup aB30 cB3 X3
  have hB1 : (∑ i : Fin 3, cB3 i • X3 (aB31 i))
      = ∑ l : Fin Nat3, D53 l • X3 l :=
    sum_smul_regroup aB31 cB3 X3
  have hwall : dLC 1 (wallChain3 : AffC 2)
      = ∑ p : Fin 32 × Fin 3, cW3 p • X3 (aW3 p) := by
    rw [wallChain3, map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cW3, ← smul_smul, ← brW3 (j, i)]
  have hbot : dLC 1 slabBot
      = (∑ i : Fin 3, cB3 i • X3 (aB30 i))
        - (∑ i : Fin 3, cB3 i • X3 (aB31 i)) := by
    rw [slabBot, map_sub, dLC_single, dLC_single]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB3, ← brB30 i]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB3, ← brB31 i]
  have hcol : dLC 1 (collarChain3 : AffC 2)
      = (∑ j : NCol3, dLC 1 (colCoef3 j • Finsupp.single (colTri3 j) (1 : ℤ)))
        - (∑ j : NCol3, dLC 1 (colCoef3 j •
            Finsupp.single (fun k => colTri3 j k + colLam3 j) (1 : ℤ))) := by
    rw [collarChain3, map_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_sub, smul_sub, map_smul, map_smul]
  have hcoef : ∀ l : Fin Nat3, D13 l - D23 l = D33 l - (D43 l - D53 l) := hcoef3
  rw [hcol, hP1, hP2, hQ1, hQ2, hwall, hW, hbot, hB0, hB1]
  exact sum_smul_four D13 D23 D33 D43 D53 X3 hcoef

end

end Work.BridgeSquare.SlabBuild

