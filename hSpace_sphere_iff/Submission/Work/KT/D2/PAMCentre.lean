import Mathlib
import Submission.Work.KT.D2.PAMDefs

namespace Work.KT.D2

/-- At the centre of the disc the Hopf idempotent is `diag(0,1)`, so the conjugation relation
`u · e₀ = PyA · u` forces the `(0,0)`-entry of `u` to vanish; invertibility of `u` then forces
the `(1,0)`-entry to be non-zero (the determinant is `-u₀₁ u₁₀`). -/
theorem PAMCentre (u : C(Work.KT.D2.Dc, Matrix (Fin 2) (Fin 2) ℂ))
    (hunit : ∀ y, IsUnit (u y))
    (hconj : ∀ y, u y * Work.KT.D2.e0 = Work.KT.D2.PyA y * u y) :
    u Work.KT.D2.dctr 0 0 = 0 ∧ u Work.KT.D2.dctr 1 0 ≠ 0 := by
  have hrel : u Work.KT.D2.dctr * Work.KT.D2.e0
      = !![(0 : ℂ), 0; 0, 1] * u Work.KT.D2.dctr := by
    rw [hconj Work.KT.D2.dctr, Work.KT.D2.PyA_ctr]
  have h00 : u Work.KT.D2.dctr 0 0 = 0 := by
    have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℂ => N 0 0) hrel
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Work.KT.D2.e0, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] at h
    simpa using h
  have h11 : u Work.KT.D2.dctr 1 1 = 0 := by
    have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℂ => N 1 1) hrel
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Work.KT.D2.e0, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] at h
    simpa using h.symm
  refine ⟨h00, ?_⟩
  intro h10
  have hdet : (u Work.KT.D2.dctr).det ≠ 0 := by
    have h := (Matrix.isUnit_iff_isUnit_det (u Work.KT.D2.dctr)).mp (hunit Work.KT.D2.dctr)
    exact isUnit_iff_ne_zero.mp h
  apply hdet
  rw [Matrix.det_fin_two, h00, h11, h10]
  ring

end Work.KT.D2
