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


end

end Work.BridgeSquare.SlabBuild

