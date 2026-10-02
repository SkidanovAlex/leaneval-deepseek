import Submission.Work.ThomBordism.PontryaginThom.Orthogonal
import Submission.Work.ThomBordism.PontryaginThom.ClmContinuity
import Submission.Work.ThomBordism.PontryaginThom.continuousOn_orthProjCLM
import Submission.Work.ThomBordism.PontryaginThom.ComplementCont

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Continuity of the frame coordinates

`Orthogonal.lean` defines `frameCoords A = (AᵀA)⁻¹Aᵀ`, the extraction of the coordinates of the
orthogonal projection of a vector in the frame `A`.  This file proves

* `frameCoords_single_apply` — the explicit formula
  `frameCoords A (Pi.single j 1) i = ∑ l, ((AᵀA)⁻¹) i l * A j l`;
* `continuousOn_frameCoordsCLM` — **the frame coordinates (as a family of continuous linear maps)
  depend continuously on a continuous family of independent frames** — the companion of
  `continuousOn_orthProjCLM`, needed for the `Ainv` field of the splitting of the normal bundle of an
  immersion.
-/

open scoped Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

variable {k : ℕ}

/-- The `j`-th column of a rectangular matrix is the value of `mulVec` on the `j`-th basis vector
(the general form of `ComplementCont.mulVec_single_one_apply`). -/
theorem mulVec_single_one_apply_rect {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (b : Fin n)
    (i : Fin m) : M.mulVec (Pi.single b 1) i = M i b := by
  rw [mulVec_apply_sum']
  rw [Finset.sum_eq_single b]
  · rw [Pi.single_eq_same, mul_one]
  · intro c _ hc
    rw [Pi.single_eq_of_ne hc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- **The frame coordinates of a basis vector**, explicitly: the `i`-th coordinate is the `i`-th row
of `(AᵀA)⁻¹` paired with the `a`-th column of `A`. -/
theorem frameCoords_single_apply (A : Fin 8 → Euc (8 + k)) (a : Fin (8 + k)) (i : Fin 8) :
    frameCoords A (Pi.single a 1) i
      = ∑ l : Fin 8,
          ((Matrix.transpose (frameMat A) * frameMat A)⁻¹) i l * frameMat A a l := by
  have h1 : (Matrix.transpose (frameMat A)).mulVec (Pi.single a 1)
      = fun l => frameMat A a l := by
    funext l
    rw [mulVec_single_one_apply_rect, Matrix.transpose_apply]
  have h2 : ((Matrix.transpose (frameMat A) * frameMat A)⁻¹).mulVec
        (fun l => frameMat A a l) i
      = ∑ l : Fin 8,
          ((Matrix.transpose (frameMat A) * frameMat A)⁻¹) i l * frameMat A a l :=
    mulVec_apply_sum' _ _ _
  rw [frameCoords, LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, h1, h2]

/-- **The frame coordinates depend continuously on the base point**: for a continuous family of
linearly independent frames `F` on `s`, the family of continuous linear maps
`x ↦ (AᵀA)⁻¹Aᵀ` is continuous on `s`. -/
theorem continuousOn_frameCoordsCLM {X : Type} [TopologicalSpace X] {k : ℕ}
    (F : X → Fin 8 → Euc (8 + k)) (s : Set X)
    (hF : ContinuousOn F s) (hind : ∀ x ∈ s, LinearIndependent ℝ (F x)) :
    ContinuousOn (fun x =>
      LinearMap.toContinuousLinearMap (frameCoords (F x))) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : s => LinearMap.toContinuousLinearMap (frameCoords (F p.1)))
  rw [continuous_toContinuousLinearMap_iff]
  intro j
  rw [continuous_pi_iff]
  intro i
  have hmat : Continuous fun p : s => frameMat (F p.1) :=
    continuous_frameMat_family (fun p : s => F p.1) hF.domRestrict
  have hgram : Continuous fun p : s =>
      Matrix.transpose (frameMat (F p.1)) * frameMat (F p.1) :=
    hmat.matrix_transpose.matrix_mul hmat
  have hdet : ∀ p : s,
      (Matrix.transpose (frameMat (F p.1)) * frameMat (F p.1)).det ≠ 0 := fun p =>
    gram_det_ne_zero (frameMat (F p.1)) (frameMat_mulVec_injective (F p.1) (hind p.1 p.2))
  have hinv : Continuous fun p : s =>
      (Matrix.transpose (frameMat (F p.1)) * frameMat (F p.1))⁻¹ := by
    have h := (continuousOn_matrix_inv 8).comp (hgram.continuousOn (s := Set.univ))
      (fun p _ => hdet p)
    rwa [continuousOn_univ] at h
  have hentry : (fun p : s => frameCoords (F p.1) (Pi.single j 1) i)
      = fun p : s => ∑ l : Fin 8,
          ((Matrix.transpose (frameMat (F p.1)) * frameMat (F p.1))⁻¹) i l
            * frameMat (F p.1) j l := by
    funext p
    exact frameCoords_single_apply (F p.1) j i
  rw [hentry]
  exact continuous_finsetSum _ fun l _ => (hinv.matrix_elem i l).mul (hmat.matrix_elem j l)

end

end Work.ThomBordism.PontryaginThom
