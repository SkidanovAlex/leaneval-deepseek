import Mathlib
import Submission.Work.KT.Psi.ClsM
import Submission.Work.KT.Psi.Basic

namespace Work.KT.Psi

open Matrix

/-- `reindex` pushes through rectangular matrix multiplication. -/
lemma reindex_mul_rect_clsM {A : Type} [AddCommMonoid A] [Mul A]
    {m m' n n' p p' : Type} [Fintype n] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (g : p ≃ p') (X : Matrix m n A) (Y : Matrix n p A) :
    Matrix.reindex e f X * Matrix.reindex f g Y = Matrix.reindex e g (X * Y) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv X Y e.symm f.symm g.symm

theorem clsM_eq_of_mvN {A : Type} [Ring A] {ι κ : Type} [Fintype ι] [Fintype κ]
    {X : Matrix ι ι A} {Y : Matrix κ κ A} (hX : X * X = X) (hY : Y * Y = Y)
    {u : Matrix κ ι A} {v : Matrix ι κ A} (hvu : v * u = X) (huv : u * v = Y) :
    Work.KT.Psi.clsM ι X = Work.KT.Psi.clsM κ Y := by
  rw [clsM_eq_cls, clsM_eq_cls]
  have hX' : Mat.IsIdem
      (⟨Fintype.card ι, Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) X⟩ : Mat A) := by
    show Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) X *
        Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) X =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) X
    rw [reindex_mul_rect_clsM (Fintype.equivFin ι) (Fintype.equivFin ι) (Fintype.equivFin ι)
      X X, hX]
  have hY' : Mat.IsIdem
      (⟨Fintype.card κ, Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin κ) Y⟩ : Mat A) := by
    show Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin κ) Y *
        Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin κ) Y =
      Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin κ) Y
    rw [reindex_mul_rect_clsM (Fintype.equivFin κ) (Fintype.equivFin κ) (Fintype.equivFin κ)
      Y Y, hY]
  refine cls_eq_of_MvN hX' hY' ⟨Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) u,
    Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin κ) v, ?_, ?_⟩
  · show Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin κ) v *
        Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) u =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) X
    rw [reindex_mul_rect_clsM (Fintype.equivFin ι) (Fintype.equivFin κ) (Fintype.equivFin ι)
      v u, hvu]
  · show Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) u *
        Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin κ) v =
      Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin κ) Y
    rw [reindex_mul_rect_clsM (Fintype.equivFin κ) (Fintype.equivFin ι) (Fintype.equivFin κ)
      u v, huv]

end Work.KT.Psi
