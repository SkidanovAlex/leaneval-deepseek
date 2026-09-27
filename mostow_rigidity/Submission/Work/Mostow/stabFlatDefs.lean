import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.StabLift

/-!
# The flat action of a horospherical similarity on a horosphere

For `ξ ∈ Sph n`, a matrix `M ∈ O(n,1)` with `M θ_ξ = θ_ξ` (where `θ_ξ = (ξ,1)`) preserves every
horosphere of `ξ`, and acts on the flat coordinate `yc ξ ·` of every horosphere by an affine
isometry `y ↦ A y + v` of `ξ^⊥`.

This file collects the (purely linear-algebraic) definitions of the two objects `A` and `v` used
by that statement:  `A` is essentially "project `M` to the `θ`-orthogonal complement and read off
the spatial part", and `v` is the image of `-(1/2) η_ξ` under the same operation.

* `Work.Mostow.flatLin ξ M` is the linear part `A : E n →ₗ[ℝ] E n`.
* `Work.Mostow.flatTrans ξ M` is the translation part `v ∈ E n`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open Matrix

noncomputable section

open scoped Matrix

variable {n : ℕ}

/-- `hspat` as a linear map. -/
def hspatLin : (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] E n where
  toFun := hspat
  map_add' x y := hspat_add x y
  map_smul' c x := hspat_smul c x

/-- `wvec` as a linear map. -/
def wvecLin : E n →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ) where
  toFun := wvec
  map_add' x y := by ext z; rcases z with i | j <;> simp [wvec]
  map_smul' c x := by ext z; rcases z with i | j <;> simp [wvec]

/-- `horoProj ξ` as a linear map. -/
def horoProjLin (ξ : E n) : (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ) where
  toFun := horoProj ξ
  map_add' := horoProj_add ξ
  map_smul' := horoProj_smul ξ

/-- The linear part `A` of the action of `M` on the horospheres at `ξ`. -/
def flatLin (ξ : E n) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) : E n →ₗ[ℝ] E n :=
  hspatLin.comp ((horoProjLin ξ).comp ((mulVecLin M).comp wvecLin))

/-- The translation part `v` of the action of `M` on the horospheres at `ξ`. -/
def flatTrans (ξ : E n) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) : E n :=
  (-(1/2) : ℝ) • hspat (horoProj ξ (M.mulVec (horoEta ξ)))

@[simp] lemma hspatLin_apply (x : Fin n ⊕ Fin 1 → ℝ) : hspatLin x = hspat x := rfl
@[simp] lemma wvecLin_apply (y : E n) : wvecLin y = wvec y := rfl
@[simp] lemma horoProjLin_apply (ξ : E n) (x : Fin n ⊕ Fin 1 → ℝ) :
    horoProjLin ξ x = horoProj ξ x := rfl

@[simp] lemma flatLin_apply (ξ : E n) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (y : E n) :
    flatLin ξ M y = hspat (horoProj ξ (M.mulVec (wvec y))) := rfl

@[simp] lemma flatTrans_apply (ξ : E n) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :
    flatTrans ξ M = (-(1/2) : ℝ) • hspat (horoProj ξ (M.mulVec (horoEta ξ))) := rfl

end

end Work.Mostow
