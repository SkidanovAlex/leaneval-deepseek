import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.PadDefs
import Submission.Work.KT.Idx.PenDefs
import Submission.Work.Idx.WPenAppendDefs
import Submission.Work.Idx.wPenAppendAnalytic
import Submission.Work.Idx.wPen_append_penProj_split
import Submission.Work.Idx.MvNGen_fromBlocks

/-!
# `Work.KT.FP.append_proj_blocks` — the block structure of the append projection

For a coefficient sequence `b : Fin (d+1) → Mₙ(C(X, ℂ))` and the padded sequence
`appSeq X b = (b₀, …, b_d, 0)` (the same polynomial `q_b`, one more block), the Riesz projection
of the `(d+2)`-block companion pencil, split along
`eApp n d : BIdx n d ⊕ Fin n ≃ BIdx n (d+1)`, has the block form
`[[P, 0], [*, 0]]` where `P` is the projection of the `(d+1)`-block pencil of `b`.

Route.  `Work.Idx.Ablk`/`Work.Idx.Bblk` are the `(d+2)`-block pencil in the split
`WIdx n d ⊕ Fin n`; `Work.Idx.reindex_eb_Ablk_app`/`reindex_eb_Bblk_app` identify their
reindexing along `eb` with `wPenA X n (d+1)`/`wPenB X n (d+1) (appSeq X b)`, and
`penProjMat_reindex_append` transports `penProjMat`.  For the block pencil,
`wPen_append_penProj_split` splits its projection as `diag(P,0) + R * Z` with `Z * R = 0`,
`Z` has zero second block column, and the projection of the diagonal pencil `diag(M_b, -1)` is
`diag(P, 0)`; hence the projection is `fromBlocks20 P (Erow * Z₁₁)`, and its two "output" blocks
vanish.
-/

namespace Work.KT.FP

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

theorem append_proj_blocks (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b))
    (h' : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n (d + 1)
        + Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.appSeq X b))) :
    (∀ (i i' : BIdx n d), Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n (d + 1))
        (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.appSeq X b))
        (eApp n d (Sum.inl i)) (eApp n d (Sum.inl i'))
        = Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d b) i i')
    ∧ (∀ (i : BIdx n d) (a : Fin n), Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n (d + 1))
        (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.appSeq X b))
        (eApp n d (Sum.inl i)) (eApp n d (Sum.inr a)) = 0)
    ∧ (∀ (a a' : Fin n), Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n (d + 1))
        (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.appSeq X b))
        (eApp n d (Sum.inr a)) (eApp n d (Sum.inr a')) = 0) := by
  -- the block pencil `Ablk`/`Bblk` is a unit on the unit circle
  have hblkB : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (z • Work.Idx.Ablk X n d + Work.Idx.Bblk X n d b) := by
    intro z hz
    have hAb : Work.Idx.Ablk X n d = Matrix.reindex (Work.Idx.eb n d).symm (Work.Idx.eb n d).symm
        (Work.KT.Idx.wPenA X n (d + 1)) := by
      rw [← Work.Idx.reindex_eb_Ablk_app X n d, Work.Idx.reindex_symm_reindex_app]
    have hBb : Work.Idx.Bblk X n d b =
        Matrix.reindex (Work.Idx.eb n d).symm (Work.Idx.eb n d).symm
          (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.appSeq X b)) := by
      rw [← Work.Idx.reindex_eb_Bblk_app X n d b, Work.Idx.reindex_symm_reindex_app]
    rw [hAb, hBb, ← Work.Idx.reindex_smul_app (Work.Idx.eb n d).symm z
        (Work.KT.Idx.wPenA X n (d + 1)),
      ← Work.Idx.reindex_add_app (Work.Idx.eb n d).symm (z • Work.KT.Idx.wPenA X n (d + 1))
        (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.appSeq X b))]
    exact (Work.Idx.isUnit_reindex_iff_app (Work.Idx.eb n d).symm _).mpr (h' z hz)
  -- the block diagonal pencil `diag(M_b, -1)` is a unit on the unit circle
  have hdiagU : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (z • Work.Idx.Adiag X n d + Work.Idx.Bdiag X n d b) := by
    intro z hz
    have h1 : z • Work.Idx.Adiag X n d + Work.Idx.Bdiag X n d b =
        Matrix.fromBlocks (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b) 0 0
          (-1) := by
      rw [Work.Idx.Adiag, Work.Idx.Bdiag, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
      simp
    rw [h1]
    exact Work.Idx.isUnit_fromBlocks_app _ _ (h z hz) Work.Idx.isUnit_neg_one_matrix_app
  -- the projection of the block diagonal pencil is `diag(P, 0)`
  have hdiag : Work.Idx.penProjMat X (Work.Idx.Adiag X n d) (Work.Idx.Bdiag X n d b) =
      Matrix.fromBlocks
        (Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d b)) 0 0 0 := by
    have h0 : Work.Idx.penProjMat X (0 : Matrix (Fin n) (Fin n) C(X, ℂ)) (-1) = 0 :=
      Work.Idx.penProjMat_zero_neg_one_app X
    have hneg : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • (0 : Matrix (Fin n) (Fin n) C(X, ℂ)) + (-1)) :=
      fun _ _ => by simpa using Work.Idx.isUnit_neg_one_matrix_app (R := C(X, ℂ)) (κ := Fin n)
    rw [Work.Idx.Adiag, Work.Idx.Bdiag]
    rw [Work.Idx.penProjMat_fromBlocks_append X (Work.KT.Idx.wPenA X n d)
      (Work.KT.Idx.wPenB X n d b) (0 : Matrix (Fin n) (Fin n) C(X, ℂ)) (-1) h hneg]
    rw [h0]
  -- the split of the projection of the `(d+2)`-block pencil
  obtain ⟨hsplit1, hZR⟩ := Work.Idx.wPen_append_penProj_split X n d b hdiagU
  -- the last `n` columns of `Z` vanish
  have hZcol : ∀ (i : Work.Idx.WIdx n d ⊕ Fin n) (y : Fin n),
      Work.Idx.Zmat X n d b i (Sum.inr y) = 0 := by
    intro i y
    have hZ := congrFun (congrFun hZR i) (Sum.inl (Work.Idx.dIdx d, y))
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at hZ
    have h1 : (∑ p : Work.Idx.WIdx n d, Work.Idx.Zmat X n d b i (Sum.inl p) *
        Work.Idx.Rmat X n d (Sum.inl p) (Sum.inl (Work.Idx.dIdx d, y))) = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [Work.Idx.Rmat, Matrix.fromBlocks_apply₁₁]
      simp
    have h2 : (∑ x : Fin n, Work.Idx.Zmat X n d b i (Sum.inr x) *
        Work.Idx.Rmat X n d (Sum.inr x) (Sum.inl (Work.Idx.dIdx d, y))) =
        Work.Idx.Zmat X n d b i (Sum.inr y) := by
      rw [Finset.sum_eq_single y]
      · rw [Work.Idx.Rmat, Matrix.fromBlocks_apply₂₁]
        simp [Work.Idx.Erow_apply]
      · intro x _ hx
        rw [Work.Idx.Rmat, Matrix.fromBlocks_apply₂₁]
        simp [Work.Idx.Erow_apply, hx]
      · intro hy
        exact absurd (Finset.mem_univ y) hy
    rw [h1, h2, zero_add] at hZ
    exact hZ
  have hZ12 : (Work.Idx.Zmat X n d b).toBlocks₁₂ = 0 := by
    refine Matrix.ext fun i y => ?_
    exact hZcol (Sum.inl i) y
  -- the block structure of the projection of the `(d+2)`-block pencil
  have hstruct : Work.Idx.penProjMat X (Work.Idx.Ablk X n d) (Work.Idx.Bblk X n d b) =
      Work.Idx.fromBlocks20
        (Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d b))
        (Work.Idx.Erow X n d * (Work.Idx.Zmat X n d b).toBlocks₁₁) := by
    rw [hsplit1, hdiag]
    have hZ : Work.Idx.Zmat X n d b = Matrix.fromBlocks (Work.Idx.Zmat X n d b).toBlocks₁₁ 0
        (Work.Idx.Zmat X n d b).toBlocks₂₁ (Work.Idx.Zmat X n d b).toBlocks₂₂ := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Work.Idx.Zmat X n d b)]
      rw [hZ12]
    rw [hZ, Work.Idx.Rmat, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
    rw [Matrix.fromBlocks_add]
    simp [Work.Idx.fromBlocks20]
  -- `eApp` and `eb` are the same equivalence
  have heApp : (eApp n d : BIdx n d ⊕ Fin n ≃ BIdx n (d + 1)) =
      (Work.Idx.eb n d : Work.Idx.WIdx n d ⊕ Fin n ≃ Fin (d + 2) × Fin n) := by
    refine Equiv.ext fun x => ?_
    rcases x with ⟨a, y⟩ | a
    · simp only [eApp_inl, Work.Idx.eb_inl]
    · simp only [eApp_inr, Work.Idx.eb_inr, Work.Idx.lastIdx]
      exact Prod.ext (Fin.eq_of_val_eq rfl) rfl
  -- the projection of the padded pencil, in block form
  have hmain : Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n (d + 1))
      (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.appSeq X b)) =
      Matrix.reindex (Work.Idx.eb n d) (Work.Idx.eb n d)
        (Work.Idx.fromBlocks20
          (Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d b))
          (Work.Idx.Erow X n d * (Work.Idx.Zmat X n d b).toBlocks₁₁)) := by
    rw [← Work.Idx.reindex_eb_Ablk_app X n d, ← Work.Idx.reindex_eb_Bblk_app X n d b,
      Work.Idx.penProjMat_reindex_append X (Work.Idx.eb n d) (Work.Idx.Ablk X n d)
        (Work.Idx.Bblk X n d b) hblkB, hstruct]
  -- entries of a `reindex`ed matrix at `eb`-images
  have hentry : ∀ (M : Matrix (Work.Idx.WIdx n d ⊕ Fin n) (Work.Idx.WIdx n d ⊕ Fin n) C(X, ℂ))
      (x y : Work.Idx.WIdx n d ⊕ Fin n),
      (Matrix.reindex (Work.Idx.eb n d) (Work.Idx.eb n d) M)
        (Work.Idx.eb n d x) (Work.Idx.eb n d y) = M x y := by
    intro M x y
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro i i'
    rw [hmain, heApp, hentry]
    exact Work.Idx.fromBlocks20_apply_inl_inl _ _ i i'
  · intro i a
    rw [hmain, heApp, hentry]
    exact Work.Idx.fromBlocks20_apply_inl_inr _ _ i a
  · intro a a'
    rw [hmain, heApp, hentry]
    exact Work.Idx.fromBlocks20_apply_inr_inr _ _ a a'

end

end Work.KT.FP
