import Mathlib
import Submission.Work.ThomBordism._gtd.P1
import Submission.Work.ThomBordism.Grassmann.Oriented

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The orientation flip is equivariant for the corrected transition functions

`coordChangeO S T` are the transition functions of the orientation-corrected tautological bundle
`tautologicalBundle k m` over the oriented Grassmannian `G̃r_k(ℝ^{k+m})` (the gluing data of the
naive presentation multiplied by the fibrewise sign gauge `orientMat`).  The orientation reversal
`ogFlip k m` right-multiplies frames by the diagonal matrix `flipMat k = diag(-1,1,…,1)`; the
statement proved here,

`coordChangeO S T (ogFlip x) ∘ flipMat = flipMat ∘ coordChangeO S T x`,

is exactly the cocycle condition that makes the construction of the orientation-reversing bundle
automorphism of the tautological bundle (the lemma `flipMap` in this directory) well defined.

The proof is a computation with the representatives: a frame `f` of `x` is sent to
`soActFun (flipMat k) f`, so `frameMatrix S` is right-multiplied by `flipMat k`, whence

* the (naive) transition matrix `frameMatrix T f * (frameMatrix S f)⁻¹` is *unchanged*, and
* the sign `frameSign S` — and therefore the gauge `orientMat S` — is multiplied by `-1`
  (`orientMat S (ogFlip x) = flipMat k * orientMat S x`).

The two effects combine to give the identity.
-/

namespace Work.ThomBordism.Signs

open Work.ThomBordism.Grassmann

namespace CoordFlip

variable {k m : ℕ}

/-! ## The determinant of `flipMat` -/

/-- The orientation reversing diagonal matrix has determinant `-1` in positive dimension. -/
theorem flipMat_det {k : ℕ} (hk : 0 < k) : (flipMat k).det = -1 := by
  rw [flipMat, Matrix.det_diagonal]
  refine (Finset.prod_eq_single (⟨0, hk⟩ : Fin k) ?_ ?_).trans ?_
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_pos rfl]

/-! ## The sign gauge as a diagonal matrix and its commutation with `flipMat` -/

/-- The sign gauge is the diagonal matrix `diag(ε,1,…,1)` with `ε = frameSign S x` (uniformly in
`k`, including `k = 0` where both sides are the unique `0 × 0` matrix). -/
theorem orientMat_diagonal (S : ChartIdx k m) (x : OG k m) :
    orientMat S x
      = Matrix.diagonal (fun i : Fin k => if (i : ℕ) = 0 then frameSign S x else 1) := by
  by_cases h : k = 0
  · subst h
    exact Subsingleton.elim _ _
  · rw [orientMat_of_ne_zero h]
    congr 1
    funext i
    by_cases hi : i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k)
    · rw [if_pos hi, if_pos (by rw [hi])]
    · rw [if_neg hi, if_neg (fun hh => hi (Fin.ext hh))]

/-- The sign gauge commutes with `flipMat` (both are diagonal). -/
theorem flipMat_mul_orientMat (S : ChartIdx k m) (x : OG k m) :
    flipMat k * orientMat S x = orientMat S x * flipMat k := by
  rw [orientMat_diagonal, flipMat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_eq_diagonal_iff]
  intro i
  ring

/-! ## The behaviour of the sign under the orientation flip -/

/-- The sign `frameSign S` changes sign under `ogFlip` in positive dimension. -/
theorem frameSign_ogFlip {k m : ℕ} (hk : k ≠ 0) (S : ChartIdx k m) (x : OG k m) :
    frameSign S (ogFlip k m x) = - frameSign S x := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  rw [ogFlip_mk, frameSign_mk, frameSign_mk, frameSignFun, frameSignFun,
    frameMatrix_soActFun, Matrix.det_mul, flipMat_det (Nat.pos_of_ne_zero hk)]
  rw [abs_mul, abs_neg, abs_one, mul_one]
  ring

/-- The sign gauge at the orientation-flipped point is the gauge at the point multiplied by
`flipMat`: `orientMat S (ogFlip x) = flipMat k * orientMat S x`. -/
theorem orientMat_ogFlip (S : ChartIdx k m) (x : OG k m) :
    orientMat S (ogFlip k m x) = flipMat k * orientMat S x := by
  rw [orientMat_diagonal, orientMat_diagonal, flipMat, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_eq_diagonal_iff]
  intro i
  by_cases hi : (i : ℕ) = 0
  · have hk : k ≠ 0 := by
      intro h; subst h; exact Fin.elim0 i
    rw [if_pos hi, if_pos hi, if_pos hi, frameSign_ogFlip hk S x]
    ring
  · rw [if_neg hi, if_neg hi, if_neg hi]
    simp

/-! ## The (naive) transition function is invariant under the orientation flip -/

/-- The transition function of the tautological bundle does not change under `ogFlip`: the frame
matrix is right-multiplied by the invertible matrix `flipMat k`, and `(A F) (B F)⁻¹ = A B⁻¹`. -/
theorem coordChange_ogFlip (S T : ChartIdx k m) (x : OG k m) :
    coordChange S T (ogFlip k m x) = coordChange S T x := by
  have hdetF : (flipMat k).det ≠ 0 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hone : flipMat 0 = 1 := Subsingleton.elim _ _
      rw [hone, Matrix.det_one]; norm_num
    · rw [flipMat_det hk]; norm_num
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  rw [ogFlip_mk, coordChange_mk, coordChange_mk, coordChangeAux, coordChangeAux]
  by_cases hA : (frameMatrix S f.1).det = 0
  · have hA' : (frameMatrix S (soActFun (flipMat k) f.1)).det = 0 := by
      rw [frameMatrix_soActFun, Matrix.det_mul, hA, zero_mul]
    rw [dif_neg (fun hh => hh hA'), dif_neg (fun hh => hh hA)]
  · rw [dif_pos hA]
    rw [dif_pos (by rw [frameMatrix_soActFun, Matrix.det_mul]; exact mul_ne_zero hA hdetF)]
    apply congrArg matLin
    rw [frameMatrix_soActFun, frameMatrix_soActFun, Matrix.mul_inv_rev,
      Matrix.inv_eq_left_inv (flipMat_mul_self k)]
    calc frameMatrix T f.1 * flipMat k * (flipMat k * (frameMatrix S f.1)⁻¹)
        = frameMatrix T f.1 * (flipMat k * flipMat k) * (frameMatrix S f.1)⁻¹ := by
          noncomm_ring
      _ = frameMatrix T f.1 * (frameMatrix S f.1)⁻¹ := by
            rw [flipMat_mul_self, Matrix.mul_one]

end CoordFlip

/-! ## The main statement -/

theorem coordChangeO_ogFlip_mul_flipMat {k m : ℕ} (S T : Work.ThomBordism.Grassmann.ChartIdx k m) {x : Work.ThomBordism.Grassmann.OG k m}
    (hx : x ∈ Work.ThomBordism.Grassmann.baseSet S ∩ Work.ThomBordism.Grassmann.baseSet T) :
    (Work.ThomBordism.Grassmann.coordChangeO S T (Work.ThomBordism.Grassmann.ogFlip k m x)).comp (Work.ThomBordism.Grassmann.matLin (Work.ThomBordism.Grassmann.flipMat k))
      = (Work.ThomBordism.Grassmann.matLin (Work.ThomBordism.Grassmann.flipMat k)).comp (Work.ThomBordism.Grassmann.coordChangeO S T x) := by
  have hC : coordChange S T (ogFlip k m x) = coordChange S T x := CoordFlip.coordChange_ogFlip S T x
  have hFF : (matLin (flipMat k)).comp (matLin (flipMat k)) = 1 := by
    rw [← matLin_mul, flipMat_mul_self, matLin_one]
  have hcomm : (matLin (flipMat k)).comp (matLin (orientMat S x))
      = (matLin (orientMat S x)).comp (matLin (flipMat k)) := by
    rw [← matLin_mul, ← matLin_mul, CoordFlip.flipMat_mul_orientMat S x]
  rw [coordChangeO, coordChangeO, hC, CoordFlip.orientMat_ogFlip T x, CoordFlip.orientMat_ogFlip S x,
      matLin_mul, matLin_mul]
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  have h1 : (matLin (orientMat S x)) ((matLin (flipMat k)) ((matLin (flipMat k)) v))
      = (matLin (orientMat S x)) v := by
    have h3 : (matLin (flipMat k)) ((matLin (flipMat k)) v) = v := by
      have := congrArg (fun f : Amb k →L[ℝ] Amb k => f v) hFF
      simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using this
    rw [h3]
  have h2 : (matLin (flipMat k)) ((matLin (orientMat S x)) ((matLin (flipMat k)) v))
      = (matLin (orientMat S x)) ((matLin (flipMat k)) ((matLin (flipMat k)) v)) := by
    have := congrArg (fun f : Amb k →L[ℝ] Amb k => f ((matLin (flipMat k)) v)) hcomm
    simpa only [ContinuousLinearMap.comp_apply] using this
  rw [h2, h1]

end Work.ThomBordism.Signs
