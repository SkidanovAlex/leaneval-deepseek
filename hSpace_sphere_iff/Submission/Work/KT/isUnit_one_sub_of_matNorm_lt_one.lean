import Mathlib

namespace Work.KT

theorem isUnit_one_sub_of_matNorm_lt_one {R : Type*} [NormedRing R] [CompleteSpace R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R)
    (hA : (Finset.univ.sup fun i => ∑ j : Fin n, ‖A i j‖₊ : NNReal) < 1) : IsUnit (1 - A) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) R) := Matrix.linftyOpNormedRing
  have hc : CompleteSpace (Matrix (Fin n) (Fin n) R) := Matrix.instCompleteSpace _ _ _
  haveI : HasSummableGeomSeries (Matrix (Fin n) (Fin n) R) :=
    @instHasSummableGeomSeriesOfCompleteSpace (Matrix (Fin n) (Fin n) R) _ hc
  have h : ‖A‖₊ < 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    exact hA
  have h' : ‖A‖ < 1 := by
    have := h
    rw [← NNReal.coe_lt_coe] at this
    simpa using this
  exact isUnit_one_sub_of_norm_lt_one h'

end Work.KT
