import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.deTurck.gramInv_mvfderiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- **Transport of `pdR` through the matrix inverse.**

For a smooth family `X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ` which is invertible at the point
`z`, the partial derivative of an entry of the inverse matrix is given by
`∂_c (X⁻¹)_{ij} = -∑_{p,q} (X⁻¹)_{ip} ∂_c X_{pq} (X⁻¹)_{qj}`.

The proof uses the (proved) general lemma `Work.Diff.STE.deTurck.fderiv_matrix_inv_entry` about the
derivative of the entrywise inverse of a matrix family, together with the smoothness of the matrix
inverse (`Work.Diff.EXT.contDiffAt_matrix_inv_pi`) to obtain differentiability. -/
theorem transport_inv_pdR {n : ℕ} (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y => X y i j))
    {z : Fin n → ℝ} (hdet : (X z).det ≠ 0) (c : Fin n) (i j : Fin n) :
    Work.Diff.STE.pdR c (fun y => ((X y)⁻¹) i j) z
      = -∑ p, ∑ q, ((X z)⁻¹) i p * (Work.Diff.STE.pdR c (fun y => X y p q) z) * ((X z)⁻¹) q j := by
  -- the family, read as a pi-valued function
  have hAcont : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => fun p q => X y p q) := by
    rw [contDiff_pi]; intro p
    rw [contDiff_pi]; intro q
    exact hX p q
  have hAdiff : DifferentiableAt ℝ (fun y : Fin n → ℝ => fun p q => X y p q) z :=
    (hAcont.contDiffAt (x := z)).differentiableAt (by simp)
  -- continuity of the determinant, so that the matrix stays invertible near `z`
  have hdetcont : ContinuousAt (fun y : Fin n → ℝ => (Matrix.of (fun p q => X y p q)).det) z :=
    (((Work.Diff.EXT.contDiff_matrix_det_pi (n := n)).comp hAcont).continuous).continuousAt
  have hdetz : (Matrix.of (fun p q => X z p q)).det ≠ 0 := hdet
  -- smoothness (hence differentiability) of the inverse family
  have hNdiff : DifferentiableAt ℝ
      (fun y : Fin n → ℝ => fun p q => (Matrix.of (fun p q => X y p q))⁻¹ p q) z :=
    (((Work.Diff.EXT.contDiffAt_matrix_inv_pi (n := n) (fun p q => X z p q) hdetz).comp z
      hAcont.contDiffAt)).differentiableAt (by simp)
  have hmul : ∀ᶠ y in nhds z,
      (Matrix.of (fun p q => X y p q))⁻¹ * Matrix.of (fun p q => X y p q) = 1 := by
    filter_upwards [hdetcont.eventually_ne hdetz] with y hy
    exact Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hy)
  have hmul' : Matrix.of (fun p q => X z p q) * (Matrix.of (fun p q => X z p q))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hdetz)
  -- the general derivative formula for the inverse of a matrix family
  have hcore := Work.Diff.STE.deTurck.fderiv_matrix_inv_entry (E := Fin n → ℝ) (n := n)
    (A := fun y p q => X y p q) (y := z) i j hAdiff hNdiff hmul hmul' (Pi.single c 1)
  have hLHS : (fun x : Fin n → ℝ => (Matrix.of ((fun y p q => X y p q) x))⁻¹ i j)
      = (fun y : Fin n → ℝ => (X y)⁻¹ i j) := by
    funext x; rfl
  simp only [Work.Diff.STE.pdR]
  rw [← hLHS, hcore]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [← Work.Diff.STE.deTurck.fderiv_pi_entry hAdiff p q (Pi.single c 1)]
  rfl

end Work.Diff.STE.B3
