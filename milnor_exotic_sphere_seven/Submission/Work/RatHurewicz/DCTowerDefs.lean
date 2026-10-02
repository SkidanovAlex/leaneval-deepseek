import Mathlib
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.RatHurewicz.degenFaces
import Submission.Work.RatHurewicz.faceComm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Degeneracy-compatible filling towers

A `Work.RatHurewicz.DCTower x₀ N` is a filling tower `Work.RatHurewicz.Tower x₀ N` whose fillings of
*degenerate* cubes are the degenerate extensions of the fillings of the underlying cubes:

`hDC : Kf (m+1) (degenOp j φ) = degenOp (Fin.castSucc j) (Kf m φ)`.

This file contains the definition and the elementary `Fin`-index lemmas used to manipulate the
degenerate extension `degenOp (Fin.castSucc j) ψ` of an `(m+1)`-cube `ψ`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- A filling tower whose fillings of degenerate cubes are the degenerate extensions of the
fillings of the underlying cubes. -/
structure DCTower (x₀ : X) (N : ℕ) extends Tower x₀ N where
  hDC : ∀ m, m + 1 ≤ N → ∀ (j : Fin (m + 1)) (φ : C(IC m, X)),
    Kf (m + 1) (degenOp j φ) = degenOp (Fin.castSucc j) (Kf m φ)

/-! ## The faces of a degenerate extension -/

/-- The top/bottom face of the degenerate extension: freezing the *last* coordinate of
`degenOp (Fin.castSucc j) ψ` gives `degenOp j` of the corresponding face of `ψ`. -/
theorem dcTower_last_face (m : ℕ) (j : Fin (m + 1)) (ψ : C(IC (m + 1), X)) (b : unitInterval) :
    (degenOp (Fin.castSucc j) ψ).comp (faceCM (Fin.last (m + 1)) b)
      = degenOp j (ψ.comp (faceCM (Fin.last m) b)) := by
  have hne : Fin.last (m+1) ≠ (Fin.castSucc j : Fin (m+2)) := by
    intro h; have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at this; omega
  rw [degenOp_comp_faceCM (i := (Fin.castSucc j : Fin (m+2))) (j := Fin.last (m+1))
        (hij := hne) (χ := ψ) (b := b)]
  have h1 : delIdx (Fin.last (m+1)) (Fin.castSucc j) (Ne.symm hne) = j := by
    apply Fin.ext
    rw [delIdx_val]
    simp only [Fin.val_castSucc, Fin.val_last]
    split_ifs <;> omega
  have h2 : delIdx (Fin.castSucc j) (Fin.last (m+1)) hne = Fin.last m := by
    apply Fin.ext
    rw [delIdx_val]
    simp only [Fin.val_castSucc, Fin.val_last]
    split_ifs <;> omega
  rw [h1, h2]

/-- The index of `castSucc j'` after deleting `castSucc i` is the `castSucc` of the index of `j'`
after deleting `i`. -/
theorem castSucc_ne {m : ℕ} {i j' : Fin (m + 1)} (hij : j' ≠ i) :
    (Fin.castSucc j' : Fin (m + 2)) ≠ Fin.castSucc i := by
  intro hh
  exact hij (Fin.ext (by
    have := congrArg Fin.val hh
    simpa only [Fin.val_castSucc] using this))

theorem delIdx_castSucc_castSucc {m : ℕ} (i j' : Fin (m + 1)) (hij : j' ≠ i) :
    delIdx (Fin.castSucc i) (Fin.castSucc j') (castSucc_ne hij)
      = Fin.castSucc (delIdx i j' hij) := by
  apply Fin.ext
  simp only [delIdx_val, Fin.val_castSucc]

/-- A side face of a degenerate extension, with the degenerate indices made explicit. -/
theorem dcTower_side_face (m : ℕ) (j ℓ : Fin (m + 1)) (ψ : C(IC (m + 1), X))
    (b : unitInterval) (hjℓ : ℓ ≠ j) (hℓj : j ≠ ℓ) :
    (degenOp (Fin.castSucc j) ψ).comp (faceCM (Fin.castSucc ℓ) b)
      = degenOp (Fin.castSucc (delIdx ℓ j hℓj))
          (ψ.comp (faceCM (Fin.castSucc (delIdx j ℓ hjℓ)) b)) := by
  have hne : (Fin.castSucc ℓ : Fin (m+2)) ≠ Fin.castSucc j := castSucc_ne hjℓ
  rw [degenOp_comp_faceCM (i := (Fin.castSucc j : Fin (m+2))) (j := Fin.castSucc ℓ)
        (hij := hne) (χ := ψ) (b := b)]
  have e1 : delIdx (Fin.castSucc ℓ) (Fin.castSucc j) (Ne.symm hne)
      = Fin.castSucc (delIdx ℓ j hℓj) := delIdx_castSucc_castSucc ℓ j hℓj
  have e2 : delIdx (Fin.castSucc j) (Fin.castSucc ℓ) hne
      = Fin.castSucc (delIdx j ℓ hjℓ) := delIdx_castSucc_castSucc j ℓ hjℓ
  rw [e1, e2]

end

end Work.RatHurewicz
