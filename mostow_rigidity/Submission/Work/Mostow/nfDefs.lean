import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.StabHoroForm

/-!
# Shared definitions for the normal form of an isometry fixing a boundary point

`g : PO n 1` with `bd g ξ = ξ` acts on the horospheres at `ξ` as a
"horospherical similarity": it multiplies the horospherical level `lev ξ` by a constant `b`
and acts on the flat coordinate `yc ξ` as `y ↦ b⁻¹ • A y + v`, with `A` a linear isometry of
`ξ^⊥` and `v ∈ ξ^⊥`.

This file collects the vocabulary and the two unconditional linear-algebra facts on which the
proof of `Work.Mostow.normalForm` is built:

* `nf_hlift_smul` : the lift of the action of `g` is given by the matrix `emat g`;
* `nfA` : the candidate linear part `A` of the normal form, `y ↦ sp (horoProj ξ (emat g *ᵥ wvec y))`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- The lift of the action of `g` on the hyperboloid is the linear action of `emat g`. -/
theorem nf_hlift_smul (g : PO n 1) (u : E n) : hlift (g • u) = emat g *ᵥ hlift u := by
  show hlift (actO (rep g) u) = emat g *ᵥ hlift u
  rw [Hyper.hlift_actO, emat, Matrix.smul_mulVec]

/-- `emat g` is `J`-orthogonal. -/
theorem nf_emat_isJOrth (g : PO n 1) :
    (emat g)ᵀ * pmOneMat * emat g = pmOneMat := by
  have h : tsign (rep g) * tsign (rep g) = (1 : ℝ) := tsign_sq (rep g)
  calc (emat g)ᵀ * pmOneMat * emat g
      = (tsign (rep g) * tsign (rep g)) • ((mat (rep g))ᵀ * pmOneMat * mat (rep g)) := by
        simp only [emat, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = pmOneMat := by rw [h, one_smul, O1_form_col]

/-- `A *ᵥ ·` as a linear map. -/
def nfMulVecLin (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :
    (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ) where
  toFun v := M *ᵥ v
  map_add' v w := Matrix.mulVec_add M v w
  map_smul' c v := Matrix.mulVec_smul M c v

/-- `y ↦ (y,0)` as a linear map into `ℝ^{n} ⊕ ℝ`. -/
def nfWvecLin : E n →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ) where
  toFun y := wvec y
  map_add' y z := by ext i; rcases i with k | k <;> simp [wvec]
  map_smul' c y := by ext i; rcases i with k | k <;> simp [wvec]

/-- The orthogonal projection onto `V^⊥ = span{θ,η}^⊥` as a linear map. -/
def nfHoroProjLin (ξ : E n) : (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ) where
  toFun x := horoProj ξ x
  map_add' := horoProj_add ξ
  map_smul' := horoProj_smul ξ

/-- The spatial part as a linear map. -/
def nfSpatLin : (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] E n where
  toFun x := hspat x
  map_add' := hspat_add
  map_smul' := hspat_smul

/-- The candidate linear part of the normal form of `g` at `ξ`:
`y ↦ sp (horoProj ξ (emat g *ᵥ (y,0)))`. -/
def nfA (ξ : E n) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) : E n →ₗ[ℝ] E n :=
  nfSpatLin.comp ((nfHoroProjLin ξ).comp ((nfMulVecLin M).comp nfWvecLin))

/-- The `V^⊥`-part of `emat g *ᵥ η`, the "translation" parameter of the normal form. -/
def nfS (ξ : E n) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) : Fin n ⊕ Fin 1 → ℝ :=
  horoProj ξ (M *ᵥ horoEta ξ)

@[simp] lemma nfA_apply (ξ : E n) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (y : E n) :
    nfA ξ M y = hspat (horoProj ξ (M *ᵥ wvec y)) := rfl

@[simp] lemma nfS_def (ξ : E n) (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :
    nfS ξ M = horoProj ξ (M *ᵥ horoEta ξ) := rfl

@[simp] lemma nfMulVecLin_apply (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (v : Fin n ⊕ Fin 1 → ℝ) : nfMulVecLin M v = M *ᵥ v := rfl

@[simp] lemma nfWvecLin_apply (y : E n) : nfWvecLin y = wvec y := rfl

@[simp] lemma nfHoroProjLin_apply (ξ : E n) (x : Fin n ⊕ Fin 1 → ℝ) :
    nfHoroProjLin ξ x = horoProj ξ x := rfl

@[simp] lemma nfSpatLin_apply (x : Fin n ⊕ Fin 1 → ℝ) : nfSpatLin x = hspat x := rfl

end

end Work.Mostow
