import Mathlib
import Submission.Work.LT.good_base_defs

/-!
# Bilinear-form set up for `Work.LT.gb_rank_le` (Kalachev--Panteleev Lemma 8)

This file provides the auxiliary definitions used in the proof of
`Work.LT.gb_rank_le`: the dot-product bilinear form `GB.dotForm` on `Fin D → ZMod 2`,
the "multiply by the matrix `x`" linear map `GB.matVecLin`, and the matrix transpose
`GB.matTranspose`.

The proof of Lemma 8 uses the orthogonal complement with respect to `GB.dotForm`:
`x ∈ CA ⊞ CB` implies that `xᵀ` maps `CA^⊥` into `CB ∩ rowSpan x`, and the dimension
count `dim (xᵀ CA^⊥) = matRank x - dim (CA ∩ colSpan x)` finishes the job.
-/

namespace Work.LT

namespace GB

variable {D : ℕ}

/-- The dot-product bilinear form on `Fin D → ZMod 2`. -/
def dotForm (D : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin D → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) (fun u v => dot u v)
    (fun u₁ u₂ v => by simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring_nf)
    (fun u v₁ v₂ => by simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring_nf)

@[simp] lemma dotForm_apply (u v : Fin D → ZMod 2) : dotForm D u v = dot u v := rfl

/-- The linear map `v ↦ x * v` (matrix-vector product). -/
def matVecLin (x : Fin D × Fin D → ZMod 2) :
    (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) where
  toFun := matVec x
  map_add' u v := by
    ext i
    simp only [matVec, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    ext i
    simp only [matVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [RingHom.id_apply]; ring

@[simp] lemma matVecLin_apply (x : Fin D × Fin D → ZMod 2) (v : Fin D → ZMod 2) :
    matVecLin x v = matVec x v := rfl

/-- The transpose of a matrix. -/
def matTranspose (x : Fin D × Fin D → ZMod 2) : Fin D × Fin D → ZMod 2 :=
  fun ij => x (ij.2, ij.1)

@[simp] lemma matTranspose_apply (x : Fin D × Fin D → ZMod 2) (i j : Fin D) :
    matTranspose x (i, j) = x (j, i) := rfl

lemma dot_comm (u v : Fin D → ZMod 2) : dot u v = dot v u := by
  simp only [dot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The dot-product form is symmetric. -/
lemma dotForm_isSymm (D : ℕ) : (dotForm D).IsSymm :=
  ⟨fun u v => dot_comm u v⟩

lemma dotForm_isRefl (D : ℕ) : (dotForm D).IsRefl := (dotForm_isSymm D).isRefl

/-- The dot product is non-degenerate. -/
lemma dot_left_separating (u : Fin D → ZMod 2) (h : ∀ v, dot u v = 0) : u = 0 := by
  funext i
  have h1 : dot u (Pi.single i 1) = 0 := h _
  have h2 : dot u (Pi.single i 1) = u i := by
    simp only [dot]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [h2] at h1
  exact h1

lemma dotForm_nondegenerate (D : ℕ) : (dotForm D).Nondegenerate :=
  ⟨fun u h => dot_left_separating u fun v => h v,
   fun u h => dot_left_separating u fun v => by
      rw [dot_comm]; exact h v⟩

end GB

end Work.LT
