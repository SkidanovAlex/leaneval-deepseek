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

/-! ## The collar identity of cusp `1`

`D1`..`D5`  are the coefficient tables of the five pieces of the identity
`dLC 1 collarChain1 = dLC 1 wallChain1 - dLC 1 slabBot`, indexed by the *atoms* (the
directed edges) `B1`, and `aC1`..`aB11` are the atom of each slot of each piece.  The
identity is then the pointwise identity of the coefficients `D1 - D2 = D3 - (D4 - D5)`.
-/

/-- The number of distinct atoms of the collar identity of cusp `1`. -/
abbrev Nat1 : ℕ := 114
/-- The atoms (directed edges) of the collar identity of cusp `1`. -/
def B1 : Fin Nat1 → (Fin 2 → CuspE3) :=
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
def fl1 (p : Fin 24 × Fin 3) : Fin (3 * 24) :=
  ⟨3 * (p.1 : ℕ) + (p.2 : ℕ), by have h := p.1.isLt; have h2 := p.2.isLt; omega⟩
/-- The flat index of a `(j,i)` slot of the wall. -/
def flw1 (p : Fin 32 × Fin 3) : Fin (3 * 32) :=
  ⟨3 * (p.1 : ℕ) + (p.2 : ℕ), by have h := p.1.isLt; have h2 := p.2.isLt; omega⟩

def aCF1 : Fin (3 * 24) → Fin Nat1 := ![8, 1, 0, 9, 4, 0, 31, 0, 1, 47, 3, 2, 48, 4, 2, 53, 2, 3, 57, 0, 4, 58, 2, 4, 35, 10, 8, 59, 10, 9, 71, 9, 10, 71, 9, 10, 61, 12, 11, 65, 11, 12, 69, 35, 34, 70, 36, 34, 105, 34, 36, 55, 49, 47, 59, 49, 48, 62, 55, 54, 72, 61, 62, 76, 70, 69, 77, 72, 73, 84, 76, 74]
def aCF1' : Fin (3 * 24) → Fin Nat1 := ![17, 14, 13, 18, 15, 13, 40, 13, 14, 96, 88, 87, 97, 89, 87, 102, 87, 88, 64, 13, 15, 107, 87, 89, 43, 19, 17, 106, 90, 91, 84, 91, 90, 77, 18, 19, 110, 93, 92, 113, 92, 93, 81, 43, 44, 82, 45, 44, 112, 44, 45, 101, 95, 96, 106, 95, 97, 109, 101, 103, 85, 110, 109, 79, 82, 81, 86, 85, 83, 86, 79, 78]
def aWF1 : Fin (3 * 32) → Fin Nat1 := ![80, 42, 44, 80, 111, 112, 67, 29, 28, 67, 100, 99, 108, 100, 103, 108, 111, 113, 38, 29, 26, 38, 42, 41, 66, 98, 99, 66, 27, 28, 68, 104, 105, 68, 33, 34, 21, 33, 32, 21, 27, 25, 94, 104, 107, 94, 98, 102, 16, 39, 40, 16, 63, 64, 6, 24, 23, 6, 52, 51, 60, 52, 54, 60, 63, 65, 37, 24, 26, 37, 39, 41, 5, 50, 51, 5, 22, 23, 7, 56, 57, 7, 30, 31, 20, 30, 32, 20, 22, 25, 46, 56, 58, 46, 50, 53]
def aB10 : Fin 3 → Fin Nat1 := ![83, 75, 74]
def aB11 : Fin 3 → Fin Nat1 := ![78, 75, 73]

/-- The atom of the first edge family of the collar. -/
def aC1 : Fin 24 × Fin 3 → Fin Nat1 := fun p => aCF1 (fl1 p)
/-- The atom of the second edge family of the collar. -/
def aC1' : Fin 24 × Fin 3 → Fin Nat1 := fun p => aCF1' (fl1 p)
/-- The atom of the edges of the wall. -/
def aW1 : Fin 32 × Fin 3 → Fin Nat1 := fun p => aWF1 (flw1 p)

def cC1 : Fin 24 × Fin 3 → ℤ := fun p => colCoef1 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cC1' : Fin 24 × Fin 3 → ℤ := fun p => colCoef1 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cW1 : Fin 32 × Fin 3 → ℤ := fun p => coefV1 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cB1 : Fin 3 → ℤ := fun i => ((-1 : ℤ) ^ (i : ℕ))

def D11 : Fin Nat1 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aC1 p = l), cC1 p
def D21 : Fin Nat1 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aC1' p = l), cC1' p
def D31 : Fin Nat1 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aW1 p = l), cW1 p
def D41 : Fin Nat1 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aB10 p = l), cB1 p
def D51 : Fin Nat1 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aB11 p = l), cB1 p

/-- The canonical basis vector of each atom. -/
abbrev X1 : Fin Nat1 → AffC 1 := fun l => Finsupp.single (B1 l) (1 : ℤ)

set_option maxHeartbeats 0 in
theorem hcoef1_c0 : ∀ l : Fin Nat1, 0 ≤ l.val → l.val < 60 → D11 l - D21 l = D31 l - (D41 l - D51 l) := by decide +kernel
set_option maxHeartbeats 0 in
theorem hcoef1_c1 : ∀ l : Fin Nat1, 60 ≤ l.val → D11 l - D21 l = D31 l - (D41 l - D51 l) := by decide +kernel
/-- The pointwise coefficient identity of the collar of cusp `1`. -/
theorem hcoef1 : ∀ l : Fin Nat1, D11 l - D21 l = D31 l - (D41 l - D51 l) := by
  intro l
  by_cases h0 : l.val < 60
  · exact hcoef1_c0 l (by omega) h0
  exact hcoef1_c1 l (by omega)

/-- The atoms of the first edge family of the collar. -/
theorem brC1 : ∀ p : Fin 24 × Fin 3, B1 (aC1 p) = vface (k := 1) p.2 (colTri1 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j <;> fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

theorem cS1_0 : (fun k => colTri1 0 k + colLam1 0) = ![slabPt (-1/2) (1/2) (1), slabPt (-1/2) (1/4) (1), slabPt (-1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_1 : (fun k => colTri1 1 k + colLam1 1) = ![slabPt (-1/2) (1/2) (1), slabPt (-1/2) (1/4) (1), slabPt (-3/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_2 : (fun k => colTri1 2 k + colLam1 2) = ![slabPt (-1/2) (1/2) (1), slabPt (-1/4) (1/4) (1), slabPt (-1/2) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_3 : (fun k => colTri1 3 k + colLam1 3) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-1/2) (1), slabPt (1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_4 : (fun k => colTri1 4 k + colLam1 4) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-1/2) (1), slabPt (1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_5 : (fun k => colTri1 5 k + colLam1 5) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-1/4) (1), slabPt (1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem cS1_6 : (fun k => colTri1 6 k + colLam1 6) = ![slabPt (-1/2) (1/2) (1), slabPt (-3/4) (1/4) (1), slabPt (-1/2) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_7 : (fun k => colTri1 7 k + colLam1 7) = ![slabPt (1/2) (-1/2) (1), slabPt (1/4) (-3/4) (1), slabPt (1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem cS1_8 : (fun k => colTri1 8 k + colLam1 8) = ![slabPt (-1/2) (1/4) (1), slabPt (-1/4) (1/4) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS1_9 : (fun k => colTri1 9 k + colLam1 9) = ![slabPt (1/2) (-3/4) (1), slabPt (1/4) (-3/4) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS1_10 : (fun k => colTri1 10 k + colLam1 10) = ![slabPt (1/2) (-3/4) (1), slabPt (1) (0) (0), slabPt (1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_11 : (fun k => colTri1 11 k + colLam1 11) = ![slabPt (-1/2) (1/4) (1), slabPt (0) (1) (0), slabPt (-3/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_12 : (fun k => colTri1 12 k + colLam1 12) = ![slabPt (1/2) (0) (1), slabPt (1/4) (0) (1), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (0) (1) + slabPt (1) (0) (0) = slabPt (1/2) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS1_13 : (fun k => colTri1 13 k + colLam1 13) = ![slabPt (1/2) (0) (1), slabPt (1/4) (1/4) (1), slabPt (1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (0) (1) + slabPt (1) (0) (0) = slabPt (1/2) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem cS1_14 : (fun k => colTri1 14 k + colLam1 14) = ![slabPt (-1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS1_15 : (fun k => colTri1 15 k + colLam1 15) = ![slabPt (-1/4) (1/4) (1), slabPt (0) (1/4) (1), slabPt (1/4) (1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (0) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (1/4) (1/4) (1)
    rw [slabPt_add']; norm_num

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

theorem tS1_27 : (fun k => tauV1 27 k + lamV1 27) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/2) (-3/4) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_28 : (fun k => tauV1 28 k + lamV1 28) = ![slabPt (-1/4) (-3/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_29 : (fun k => tauV1 29 k + lamV1 29) = ![slabPt (-1/4) (-1/4) (1), slabPt (-1/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_30 : (fun k => tauV1 30 k + lamV1 30) = ![slabPt (-3/4) (-3/4) (1), slabPt (-3/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS1_31 : (fun k => tauV1 31 k + lamV1 31) = ![slabPt (-3/4) (-1/4) (1), slabPt (-3/4) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (3/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem brC1'_0 (i : Fin 3) : B1 (aC1' (0, i)) = vface (k := 1) i (fun k => colTri1 0 k + colLam1 0) := by
  rw [cS1_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_1 (i : Fin 3) : B1 (aC1' (1, i)) = vface (k := 1) i (fun k => colTri1 1 k + colLam1 1) := by
  rw [cS1_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_2 (i : Fin 3) : B1 (aC1' (2, i)) = vface (k := 1) i (fun k => colTri1 2 k + colLam1 2) := by
  rw [cS1_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_3 (i : Fin 3) : B1 (aC1' (3, i)) = vface (k := 1) i (fun k => colTri1 3 k + colLam1 3) := by
  rw [cS1_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_4 (i : Fin 3) : B1 (aC1' (4, i)) = vface (k := 1) i (fun k => colTri1 4 k + colLam1 4) := by
  rw [cS1_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_5 (i : Fin 3) : B1 (aC1' (5, i)) = vface (k := 1) i (fun k => colTri1 5 k + colLam1 5) := by
  rw [cS1_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_6 (i : Fin 3) : B1 (aC1' (6, i)) = vface (k := 1) i (fun k => colTri1 6 k + colLam1 6) := by
  rw [cS1_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_7 (i : Fin 3) : B1 (aC1' (7, i)) = vface (k := 1) i (fun k => colTri1 7 k + colLam1 7) := by
  rw [cS1_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_8 (i : Fin 3) : B1 (aC1' (8, i)) = vface (k := 1) i (fun k => colTri1 8 k + colLam1 8) := by
  rw [cS1_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_9 (i : Fin 3) : B1 (aC1' (9, i)) = vface (k := 1) i (fun k => colTri1 9 k + colLam1 9) := by
  rw [cS1_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_10 (i : Fin 3) : B1 (aC1' (10, i)) = vface (k := 1) i (fun k => colTri1 10 k + colLam1 10) := by
  rw [cS1_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_11 (i : Fin 3) : B1 (aC1' (11, i)) = vface (k := 1) i (fun k => colTri1 11 k + colLam1 11) := by
  rw [cS1_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_12 (i : Fin 3) : B1 (aC1' (12, i)) = vface (k := 1) i (fun k => colTri1 12 k + colLam1 12) := by
  rw [cS1_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_13 (i : Fin 3) : B1 (aC1' (13, i)) = vface (k := 1) i (fun k => colTri1 13 k + colLam1 13) := by
  rw [cS1_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_14 (i : Fin 3) : B1 (aC1' (14, i)) = vface (k := 1) i (fun k => colTri1 14 k + colLam1 14) := by
  rw [cS1_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_15 (i : Fin 3) : B1 (aC1' (15, i)) = vface (k := 1) i (fun k => colTri1 15 k + colLam1 15) := by
  rw [cS1_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_16 (i : Fin 3) : B1 (aC1' (16, i)) = vface (k := 1) i (fun k => colTri1 16 k + colLam1 16) := by
  rw [cS1_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_17 (i : Fin 3) : B1 (aC1' (17, i)) = vface (k := 1) i (fun k => colTri1 17 k + colLam1 17) := by
  rw [cS1_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_18 (i : Fin 3) : B1 (aC1' (18, i)) = vface (k := 1) i (fun k => colTri1 18 k + colLam1 18) := by
  rw [cS1_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_19 (i : Fin 3) : B1 (aC1' (19, i)) = vface (k := 1) i (fun k => colTri1 19 k + colLam1 19) := by
  rw [cS1_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_20 (i : Fin 3) : B1 (aC1' (20, i)) = vface (k := 1) i (fun k => colTri1 20 k + colLam1 20) := by
  rw [cS1_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_21 (i : Fin 3) : B1 (aC1' (21, i)) = vface (k := 1) i (fun k => colTri1 21 k + colLam1 21) := by
  rw [cS1_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_22 (i : Fin 3) : B1 (aC1' (22, i)) = vface (k := 1) i (fun k => colTri1 22 k + colLam1 22) := by
  rw [cS1_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC1'_23 (i : Fin 3) : B1 (aC1' (23, i)) = vface (k := 1) i (fun k => colTri1 23 k + colLam1 23) := by
  rw [cS1_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_0 (i : Fin 3) : B1 (aW1 (0, i)) = vface (k := 1) i (fun k => tauV1 0 k + lamV1 0) := by
  rw [tS1_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_1 (i : Fin 3) : B1 (aW1 (1, i)) = vface (k := 1) i (fun k => tauV1 1 k + lamV1 1) := by
  rw [tS1_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_2 (i : Fin 3) : B1 (aW1 (2, i)) = vface (k := 1) i (fun k => tauV1 2 k + lamV1 2) := by
  rw [tS1_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_3 (i : Fin 3) : B1 (aW1 (3, i)) = vface (k := 1) i (fun k => tauV1 3 k + lamV1 3) := by
  rw [tS1_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_4 (i : Fin 3) : B1 (aW1 (4, i)) = vface (k := 1) i (fun k => tauV1 4 k + lamV1 4) := by
  rw [tS1_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_5 (i : Fin 3) : B1 (aW1 (5, i)) = vface (k := 1) i (fun k => tauV1 5 k + lamV1 5) := by
  rw [tS1_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_6 (i : Fin 3) : B1 (aW1 (6, i)) = vface (k := 1) i (fun k => tauV1 6 k + lamV1 6) := by
  rw [tS1_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_7 (i : Fin 3) : B1 (aW1 (7, i)) = vface (k := 1) i (fun k => tauV1 7 k + lamV1 7) := by
  rw [tS1_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_8 (i : Fin 3) : B1 (aW1 (8, i)) = vface (k := 1) i (fun k => tauV1 8 k + lamV1 8) := by
  rw [tS1_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_9 (i : Fin 3) : B1 (aW1 (9, i)) = vface (k := 1) i (fun k => tauV1 9 k + lamV1 9) := by
  rw [tS1_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_10 (i : Fin 3) : B1 (aW1 (10, i)) = vface (k := 1) i (fun k => tauV1 10 k + lamV1 10) := by
  rw [tS1_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_11 (i : Fin 3) : B1 (aW1 (11, i)) = vface (k := 1) i (fun k => tauV1 11 k + lamV1 11) := by
  rw [tS1_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_12 (i : Fin 3) : B1 (aW1 (12, i)) = vface (k := 1) i (fun k => tauV1 12 k + lamV1 12) := by
  rw [tS1_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_13 (i : Fin 3) : B1 (aW1 (13, i)) = vface (k := 1) i (fun k => tauV1 13 k + lamV1 13) := by
  rw [tS1_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_14 (i : Fin 3) : B1 (aW1 (14, i)) = vface (k := 1) i (fun k => tauV1 14 k + lamV1 14) := by
  rw [tS1_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_15 (i : Fin 3) : B1 (aW1 (15, i)) = vface (k := 1) i (fun k => tauV1 15 k + lamV1 15) := by
  rw [tS1_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_16 (i : Fin 3) : B1 (aW1 (16, i)) = vface (k := 1) i (fun k => tauV1 16 k + lamV1 16) := by
  rw [tS1_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_17 (i : Fin 3) : B1 (aW1 (17, i)) = vface (k := 1) i (fun k => tauV1 17 k + lamV1 17) := by
  rw [tS1_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_18 (i : Fin 3) : B1 (aW1 (18, i)) = vface (k := 1) i (fun k => tauV1 18 k + lamV1 18) := by
  rw [tS1_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_19 (i : Fin 3) : B1 (aW1 (19, i)) = vface (k := 1) i (fun k => tauV1 19 k + lamV1 19) := by
  rw [tS1_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_20 (i : Fin 3) : B1 (aW1 (20, i)) = vface (k := 1) i (fun k => tauV1 20 k + lamV1 20) := by
  rw [tS1_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_21 (i : Fin 3) : B1 (aW1 (21, i)) = vface (k := 1) i (fun k => tauV1 21 k + lamV1 21) := by
  rw [tS1_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_22 (i : Fin 3) : B1 (aW1 (22, i)) = vface (k := 1) i (fun k => tauV1 22 k + lamV1 22) := by
  rw [tS1_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_23 (i : Fin 3) : B1 (aW1 (23, i)) = vface (k := 1) i (fun k => tauV1 23 k + lamV1 23) := by
  rw [tS1_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_24 (i : Fin 3) : B1 (aW1 (24, i)) = vface (k := 1) i (fun k => tauV1 24 k + lamV1 24) := by
  rw [tS1_24]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_25 (i : Fin 3) : B1 (aW1 (25, i)) = vface (k := 1) i (fun k => tauV1 25 k + lamV1 25) := by
  rw [tS1_25]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_26 (i : Fin 3) : B1 (aW1 (26, i)) = vface (k := 1) i (fun k => tauV1 26 k + lamV1 26) := by
  rw [tS1_26]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_27 (i : Fin 3) : B1 (aW1 (27, i)) = vface (k := 1) i (fun k => tauV1 27 k + lamV1 27) := by
  rw [tS1_27]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_28 (i : Fin 3) : B1 (aW1 (28, i)) = vface (k := 1) i (fun k => tauV1 28 k + lamV1 28) := by
  rw [tS1_28]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_29 (i : Fin 3) : B1 (aW1 (29, i)) = vface (k := 1) i (fun k => tauV1 29 k + lamV1 29) := by
  rw [tS1_29]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_30 (i : Fin 3) : B1 (aW1 (30, i)) = vface (k := 1) i (fun k => tauV1 30 k + lamV1 30) := by
  rw [tS1_30]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW1_31 (i : Fin 3) : B1 (aW1 (31, i)) = vface (k := 1) i (fun k => tauV1 31 k + lamV1 31) := by
  rw [tS1_31]; fin_cases i <;> funext k <;> fin_cases k <;> rfl

/-- The atoms of the second edge family of the collar. -/
theorem brC1' : ∀ p : Fin 24 × Fin 3,
    B1 (aC1' p) = vface (k := 1) p.2 (fun k => colTri1 p.1 k + colLam1 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brC1'_0 i, brC1'_1 i, brC1'_2 i, brC1'_3 i, brC1'_4 i, brC1'_5 i, brC1'_6 i, brC1'_7 i, brC1'_8 i, brC1'_9 i, brC1'_10 i, brC1'_11 i, brC1'_12 i, brC1'_13 i, brC1'_14 i, brC1'_15 i, brC1'_16 i, brC1'_17 i, brC1'_18 i, brC1'_19 i, brC1'_20 i, brC1'_21 i, brC1'_22 i, brC1'_23 i]

/-- The atoms of the edges of the wall. -/
theorem brW1 : ∀ p : Fin 32 × Fin 3,
    B1 (aW1 p) = vface (k := 1) p.2 (fun k => tauV1 p.1 k + lamV1 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brW1_0 i, brW1_1 i, brW1_2 i, brW1_3 i, brW1_4 i, brW1_5 i, brW1_6 i, brW1_7 i, brW1_8 i, brW1_9 i, brW1_10 i, brW1_11 i, brW1_12 i, brW1_13 i, brW1_14 i, brW1_15 i, brW1_16 i, brW1_17 i, brW1_18 i, brW1_19 i, brW1_20 i, brW1_21 i, brW1_22 i, brW1_23 i, brW1_24 i, brW1_25 i, brW1_26 i, brW1_27 i, brW1_28 i, brW1_29 i, brW1_30 i, brW1_31 i]

/-- The atoms of the first coarse triangle. -/
theorem brB10 : ∀ i : Fin 3, B1 (aB10 i) = vface (k := 1) i botV0 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

/-- The atoms of the second coarse triangle. -/
theorem brB11 : ∀ i : Fin 3, B1 (aB11 i) = vface (k := 1) i botV1 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

theorem colLam_mem1 (j : NCol1) : slabL 1 (colLam1 j) ∈ Work.Cusp.lattice 1 := by
  have h : slabL 1 (colLam1 j) ∈ ({Work.Cusp.kv 1 1, Work.Cusp.kv 1 2} : Set CuspE3) := by
    fin_cases j <;> simp [colLam1, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3]
  rcases h with h | h
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 1)
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 2)

/-- **The collar of cusp `1` is in the kernel of `slabChain`.** -/
theorem collar_slab1 : slabChain 1 2 (collarChain1 : AffC 2) = 0 := by
  rw [collarChain1, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, map_sub, slabChain_single_one, slabChain_single_one]
  have h1 : slabV 1 (fun k => colTri1 j k + colLam1 j)
      = fun k => slabV 1 (colTri1 j) k + slabL 1 (colLam1 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 1 (slabV 1 (colTri1 j)) (slabL 1 (colLam1 j))
        (colLam_mem1 j), sub_self, smul_zero]

/-- **The boundary of the collar of cusp `1`.** -/
theorem dLC_collar1 :
    dLC 1 (collarChain1 : AffC 2) = dLC 1 (wallChain1 : AffC 2) - dLC 1 slabBot := by
  have hP1 : (∑ j : NCol1, dLC 1 (colCoef1 j • Finsupp.single (colTri1 j) (1 : ℤ)))
      = ∑ p : Fin 24 × Fin 3, cC1 p • X1 (aC1 p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC1, ← smul_smul, ← brC1 (j, i)]
  have hP2 : (∑ j : NCol1, dLC 1 (colCoef1 j •
        Finsupp.single (fun k => colTri1 j k + colLam1 j) (1 : ℤ)))
      = ∑ p : Fin 24 × Fin 3, cC1' p • X1 (aC1' p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC1', ← smul_smul, ← brC1' (j, i)]
  have hQ1 : (∑ p : Fin 24 × Fin 3, cC1 p • X1 (aC1 p))
      = ∑ l : Fin Nat1, D11 l • X1 l :=
    sum_smul_regroup aC1 cC1 X1
  have hQ2 : (∑ p : Fin 24 × Fin 3, cC1' p • X1 (aC1' p))
      = ∑ l : Fin Nat1, D21 l • X1 l :=
    sum_smul_regroup aC1' cC1' X1
  have hW : (∑ p : Fin 32 × Fin 3, cW1 p • X1 (aW1 p))
      = ∑ l : Fin Nat1, D31 l • X1 l :=
    sum_smul_regroup aW1 cW1 X1
  have hB0 : (∑ i : Fin 3, cB1 i • X1 (aB10 i))
      = ∑ l : Fin Nat1, D41 l • X1 l :=
    sum_smul_regroup aB10 cB1 X1
  have hB1 : (∑ i : Fin 3, cB1 i • X1 (aB11 i))
      = ∑ l : Fin Nat1, D51 l • X1 l :=
    sum_smul_regroup aB11 cB1 X1
  have hwall : dLC 1 (wallChain1 : AffC 2)
      = ∑ p : Fin 32 × Fin 3, cW1 p • X1 (aW1 p) := by
    rw [wallChain1, map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cW1, ← smul_smul, ← brW1 (j, i)]
  have hbot : dLC 1 slabBot
      = (∑ i : Fin 3, cB1 i • X1 (aB10 i))
        - (∑ i : Fin 3, cB1 i • X1 (aB11 i)) := by
    rw [slabBot, map_sub, dLC_single, dLC_single]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB1, ← brB10 i]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB1, ← brB11 i]
  have hcol : dLC 1 (collarChain1 : AffC 2)
      = (∑ j : NCol1, dLC 1 (colCoef1 j • Finsupp.single (colTri1 j) (1 : ℤ)))
        - (∑ j : NCol1, dLC 1 (colCoef1 j •
            Finsupp.single (fun k => colTri1 j k + colLam1 j) (1 : ℤ))) := by
    rw [collarChain1, map_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_sub, smul_sub, map_smul, map_smul]
  have hcoef : ∀ l : Fin Nat1, D11 l - D21 l = D31 l - (D41 l - D51 l) := hcoef1
  rw [hcol, hP1, hP2, hQ1, hQ2, hwall, hW, hbot, hB0, hB1]
  exact sum_smul_four D11 D21 D31 D41 D51 X1 hcoef

end

end Work.BridgeSquare.SlabBuild

