import Mathlib
import Submission.Work.KT.Idx.WPen
import Submission.Work.KT.Idx.PenDefs
import Submission.Work.KT.Basic
import Submission.Work.Idx.WPenAppendDefs
import Submission.Work.Idx.wPenAppendAnalytic
import Submission.Work.Idx.MvNGen_fromBlocks
import Submission.Work.Idx.wPen_append_penProj_split

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval
open Work.KT.Idx

noncomputable section

/-- **Append a zero coefficient: the Bott index does not change.**

Hatcher's formula (1) in the "W" form: for a coefficient sequence `b : Fin (d+1) → Mₙ(C(X, ℂ))`,
the sequence `(b, 0)` (`Work.KT.Idx.appSeq X b`, the same polynomial `q_b`, one more block) has a
companion pencil of one size larger, and the class of the Riesz projection is the same: the extra
block is trivial and `E₋` of a trivial block vanishes (equivalently `((n+2)E)_- ≈ ((n+1)E)_-`).

Route.  `Work.KT.Idx.matPenProj` is defined in `Submission/Work/KT/Idx/PenDefs.lean` and its
idempotency is `Work.Idx.penProj_idem` (being proved in parallel).  Working with the *block* index
(`Fin (d+1) × Fin n`, before the `finProdFinEquiv` reindexing used by `wPenAf`/`wPenBf`, which is
`Matrix.reindex` and therefore harmless for `cls`), one computes that the pencil of `appSeq X b`
puts the extra block in a position where the projection has zero last `n` columns and top-left
block equal to the projection for `b`; the two projections are then Murray–von Neumann equivalent
(`Mat.MvN` allows rectangular witnesses) via the entry/exit matrices built from those blocks.
A useful helper is the additivity of `matPenProj` over block-diagonal pencils, and the fact that
the resolvent of a block-diagonal pencil is block-diagonal.  Useful structural lemma: for
`z ≠ 0` the kernel of the companion pencil is the kernel of `Σ_j b_j z^j` (kernel recursion
`v_{i+1} = z v_i`), and `det (companion pencil at z) = det (Σ_j b_j z^j)` — so the roots and their
multiplicities do not change under `appSeq`. -/
theorem wPen_append (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (Work.KT.Idx.wPenPencil X n d b z))
    (h' : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (Work.KT.Idx.wPenPencil X n (d + 1) (Work.KT.Idx.appSeq X b) z)) :
    Work.KT.cls (⟨(d + 2) * n, Work.KT.Idx.matPenProj X (Work.KT.Idx.wPenAf X n (d + 1))
        (Work.KT.Idx.wPenBf X n (d + 1) (Work.KT.Idx.appSeq X b))⟩ : Work.KT.Mat C(X, ℂ)) =
      Work.KT.cls (⟨(d + 1) * n, Work.KT.Idx.matPenProj X (Work.KT.Idx.wPenAf X n d)
        (Work.KT.Idx.wPenBf X n d b)⟩ : Work.KT.Mat C(X, ℂ)) := by
  -- the small pencil, in block form, is a unit on the circle
  have hblk : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • wPenA X n d + wPenB X n d b) := by
    intro z hz
    have h1 : Work.KT.Idx.wPenPencil X n d b z =
        Matrix.reindex finProdFinEquiv finProdFinEquiv (z • wPenA X n d + wPenB X n d b) := by
      simp only [Work.KT.Idx.wPenPencil, wPenAf, wPenBf, ← reindex_add_app, ← reindex_smul_app]
    have hz2 := h z hz
    rw [h1] at hz2
    exact (isUnit_reindex_iff_app finProdFinEquiv (z • wPenA X n d + wPenB X n d b)).mp hz2
  -- the large pencil, in block form, is a unit on the circle
  have hblkBig : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (z • wPenA X n (d + 1) + wPenB X n (d + 1) (appSeq X b)) := by
    intro z hz
    have h1 : Work.KT.Idx.wPenPencil X n (d + 1) (appSeq X b) z =
        Matrix.reindex finProdFinEquiv finProdFinEquiv
          (z • wPenA X n (d + 1) + wPenB X n (d + 1) (appSeq X b)) := by
      simp only [Work.KT.Idx.wPenPencil, wPenAf, wPenBf, ← reindex_add_app, ← reindex_smul_app]
    have hz2 := h' z hz
    rw [h1] at hz2
    exact (isUnit_reindex_iff_app finProdFinEquiv
      (z • wPenA X n (d + 1) + wPenB X n (d + 1) (appSeq X b))).mp hz2
  -- the same pencil in the block splitting `(WIdx) ⊕ Fin n`
  have hblkB : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Ablk X n d + Bblk X n d b) := by
    intro z hz
    have hAb : Ablk X n d =
        Matrix.reindex (eb n d).symm (eb n d).symm (wPenA X n (d + 1)) := by
      rw [← reindex_eb_Ablk_app X n d, reindex_symm_reindex_app]
    have hBb : Bblk X n d b =
        Matrix.reindex (eb n d).symm (eb n d).symm (wPenB X n (d + 1) (appSeq X b)) := by
      rw [← reindex_eb_Bblk_app X n d b, reindex_symm_reindex_app]
    rw [hAb, hBb, ← reindex_smul_app (eb n d).symm z (wPenA X n (d + 1)),
      ← reindex_add_app (eb n d).symm (z • wPenA X n (d + 1)) (wPenB X n (d + 1) (appSeq X b))]
    exact (isUnit_reindex_iff_app (eb n d).symm
      (z • wPenA X n (d + 1) + wPenB X n (d + 1) (appSeq X b))).mpr (hblkBig z hz)
  -- the block diagonal pencil is a unit on the circle
  have hdiagU : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Adiag X n d + Bdiag X n d b) := by
    intro z hz
    have h1 : z • Adiag X n d + Bdiag X n d b =
        Matrix.fromBlocks (z • wPenA X n d + wPenB X n d b) 0 0 (-1) := by
      rw [Adiag, Bdiag, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
      simp
    rw [h1]
    exact isUnit_fromBlocks_app _ _ (hblk z hz) (isUnit_neg_one_matrix_app)
  -- idempotency of both projections
  have hPidem : penProjMat X (wPenA X n d) (wPenB X n d b) *
      penProjMat X (wPenA X n d) (wPenB X n d b) =
      penProjMat X (wPenA X n d) (wPenB X n d b) :=
    penProjMat_idem_app X _ _ hblk
  have hP'idem : penProjMat X (Ablk X n d) (Bblk X n d b) *
      penProjMat X (Ablk X n d) (Bblk X n d b) =
      penProjMat X (Ablk X n d) (Bblk X n d b) :=
    penProjMat_idem_app X _ _ hblkB
  -- the projection of the block diagonal pencil
  have hdiag : penProjMat X (Adiag X n d) (Bdiag X n d b) =
      Matrix.fromBlocks (penProjMat X (wPenA X n d) (wPenB X n d b)) 0 0 0 := by
    have h0 : penProjMat X (0 : Matrix (Fin n) (Fin n) C(X, ℂ)) (-1) = 0 :=
      penProjMat_zero_neg_one_app X
    have hneg : ∀ z : ℂ, ‖z‖ = 1 →
        IsUnit (z • (0 : Matrix (Fin n) (Fin n) C(X, ℂ)) + (-1)) :=
      fun z _ => by simpa using isUnit_neg_one_matrix_app (R := C(X, ℂ)) (κ := Fin n)
    rw [Adiag, Bdiag]
    rw [penProjMat_fromBlocks_append X (wPenA X n d) (wPenB X n d b)
      (0 : Matrix (Fin n) (Fin n) C(X, ℂ)) (-1) hblk hneg]
    rw [h0]
  -- the split of the projection of the `(d+2)`-block pencil
  have hsplit := wPen_append_penProj_split X n d b hdiagU
  have hZR : Zmat X n d b * Rmat X n d = 0 := hsplit.2
  -- the last `n` columns of `Zmat` vanish
  have hZcol : ∀ (i : WIdx n d ⊕ Fin n) (y : Fin n), Zmat X n d b i (Sum.inr y) = 0 := by
    intro i y
    have h := congrFun (congrFun hZR i) (Sum.inl (dIdx d, y))
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h
    have h1 : (∑ p : WIdx n d, Zmat X n d b i (Sum.inl p) *
        Rmat X n d (Sum.inl p) (Sum.inl (dIdx d, y))) = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [Rmat, Matrix.fromBlocks_apply₁₁]
      simp
    have h2 : (∑ x : Fin n, Zmat X n d b i (Sum.inr x) *
        Rmat X n d (Sum.inr x) (Sum.inl (dIdx d, y))) = Zmat X n d b i (Sum.inr y) := by
      rw [Finset.sum_eq_single y]
      · rw [Rmat, Matrix.fromBlocks_apply₂₁]
        simp [Erow_apply]
      · intro x _ hx
        rw [Rmat, Matrix.fromBlocks_apply₂₁]
        simp [Erow_apply, hx]
      · intro hy
        exact absurd (Finset.mem_univ y) hy
    rw [h1, h2, zero_add] at h
    exact h
  have hZ12 : (Zmat X n d b).toBlocks₁₂ = 0 := by
    refine Matrix.ext fun i y => ?_
    exact hZcol (Sum.inl i) y
  -- the block structure of the projection of the `(d+2)`-block pencil
  have hstruct : penProjMat X (Ablk X n d) (Bblk X n d b) =
      fromBlocks20 (penProjMat X (wPenA X n d) (wPenB X n d b))
        (Erow X n d * (Zmat X n d b).toBlocks₁₁) := by
    rw [hsplit.1, hdiag]
    have hZ : Zmat X n d b = Matrix.fromBlocks (Zmat X n d b).toBlocks₁₁ 0
        (Zmat X n d b).toBlocks₂₁ (Zmat X n d b).toBlocks₂₂ := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Zmat X n d b)]
      rw [hZ12]
    rw [hZ, Rmat, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
    rw [Matrix.fromBlocks_add]
    simp [fromBlocks20]
  -- Murray–von Neumann equivalence of the two projections
  have hXidem : fromBlocks20 (penProjMat X (wPenA X n d) (wPenB X n d b))
      (Erow X n d * (Zmat X n d b).toBlocks₁₁) *
      fromBlocks20 (penProjMat X (wPenA X n d) (wPenB X n d b))
      (Erow X n d * (Zmat X n d b).toBlocks₁₁) =
      fromBlocks20 (penProjMat X (wPenA X n d) (wPenB X n d b))
      (Erow X n d * (Zmat X n d b).toBlocks₁₁) := by
    rw [← hstruct]
    exact hP'idem
  have hMvN : MvNGen (penProjMat X (Ablk X n d) (Bblk X n d b))
      (penProjMat X (wPenA X n d) (wPenB X n d b)) := by
    rw [hstruct]
    exact MvNGen_fromBlocks _ _ hPidem hXidem
  have hMvN1 : MvNGen (Matrix.reindex (eb n d) (eb n d) (penProjMat X (Ablk X n d) (Bblk X n d b)))
      (penProjMat X (wPenA X n d) (wPenB X n d b)) := by
    have h := (MvNGen_reindex (eb n d) (Equiv.refl (WIdx n d))
      (penProjMat X (Ablk X n d) (Bblk X n d b))
      (penProjMat X (wPenA X n d) (wPenB X n d b))).mpr hMvN
    rwa [reindex_refl_app] at h
  have hMvN2 : MvNGen
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.reindex (eb n d) (eb n d) (penProjMat X (Ablk X n d) (Bblk X n d b))))
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (penProjMat X (wPenA X n d) (wPenB X n d b))) :=
    (MvNGen_reindex finProdFinEquiv finProdFinEquiv _ _).mpr hMvN1
  -- the two projections are the reindexed block projections
  have hbr2 : Work.KT.Idx.matPenProj X (Work.KT.Idx.wPenAf X n (d + 1))
      (Work.KT.Idx.wPenBf X n (d + 1) (Work.KT.Idx.appSeq X b)) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.reindex (eb n d) (eb n d) (penProjMat X (Ablk X n d) (Bblk X n d b))) := by
    rw [matPenProj_eq_penProjMat]
    simp only [wPenAf, wPenBf]
    rw [penProjMat_reindex_append X finProdFinEquiv (wPenA X n (d + 1))
      (wPenB X n (d + 1) (appSeq X b)) hblkBig]
    congr 1
    rw [← reindex_eb_Ablk_app X n d, ← reindex_eb_Bblk_app X n d b]
    exact penProjMat_reindex_append X (eb n d) (Ablk X n d) (Bblk X n d b) hblkB
  have hbr1 : Work.KT.Idx.matPenProj X (Work.KT.Idx.wPenAf X n d)
      (Work.KT.Idx.wPenBf X n d b) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (penProjMat X (wPenA X n d) (wPenB X n d b)) := by
    rw [matPenProj_eq_penProjMat]
    simp only [wPenAf, wPenBf]
    exact penProjMat_reindex_append X finProdFinEquiv (wPenA X n d) (wPenB X n d b) hblk
  rw [hbr2, hbr1]
  refine Work.KT.cls_eq_of_mvN ?_ ?_ hMvN2
  · exact isIdem_reindex finProdFinEquiv (isIdem_reindex (eb n d) hP'idem)
  · exact isIdem_reindex finProdFinEquiv hPidem

end

end Work.Idx
