import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.LinearAlgebra.Matrix.cauchy_binet

open Matrix

namespace Commons.LinearAlgebra.Matrix

/-- The `r`-th **compound matrix** of an `N × N` matrix `A`: its rows and columns are indexed by
the `r`-element subsets of `Fin N`, and the entry in row `T` and column `S` is the minor of `A`
given by the rows in `T` and the columns in `S`, each listed in increasing order. -/
noncomputable def compound {R : Type*} [CommRing R] {N : ℕ} (r : ℕ)
    (A : Matrix (Fin N) (Fin N) R) :
    Matrix {U : Finset (Fin N) // U.card = r} {U : Finset (Fin N) // U.card = r} R :=
  Matrix.of fun T S => (A.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det

/-- The compound construction is multiplicative; this is exactly Cauchy–Binet
(`Commons.LinearAlgebra.Matrix.cauchy_binet`). -/
lemma compound_mul {R : Type*} [CommRing R] {N r : ℕ} (A B : Matrix (Fin N) (Fin N) R) :
    compound r (A * B) = compound r A * compound r B := by
  ext T S
  rw [Matrix.mul_apply]
  simp only [compound, Matrix.of_apply]
  exact cauchy_binet A B T.1 S.1 T.2 S.2

/-- The compound construction sends the identity to the identity. -/
lemma compound_one {R : Type*} [CommRing R] {N r : ℕ} :
    compound r (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  classical
  ext T S
  simp only [compound, Matrix.of_apply]
  by_cases h : T = S
  · subst h
    rw [Matrix.submatrix_one _ (T.1.orderEmbOfFin T.2).injective, Matrix.det_one]
    simp
  · have hsub : ¬ (T.1 ⊆ S.1) := by
      intro hs
      exact h (Subtype.ext (Finset.eq_of_subset_of_card_le hs (by rw [T.2, S.2])))
    rw [Finset.not_subset] at hsub
    obtain ⟨x, hxT, hxS⟩ := hsub
    have hx : x ∈ Set.range (T.1.orderEmbOfFin T.2) := by
      rw [Finset.range_orderEmbOfFin]; exact hxT
    obtain ⟨i, hi⟩ := hx
    rw [Matrix.one_apply, if_neg h]
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [Matrix.submatrix_apply, Matrix.one_apply, if_neg]
    intro hcon
    exact hxS (by rw [← hi, hcon]; exact Finset.orderEmbOfFin_mem S.1 S.2 j)

/-- **The compound matrix of an invertible matrix is invertible.**  The `r`-th compound matrix
`T, S ↦ det (A.submatrix (T.orderEmbOfFin _) (S.orderEmbOfFin _))` of a matrix `A` with
`A.det ≠ 0` has non-zero determinant.  (Immediate from Cauchy–Binet
`Commons.LinearAlgebra.Matrix.cauchy_binet`, since the compound construction is multiplicative
and sends `1` to `1`.) -/
theorem det_compound_ne_zero {R : Type*} [Field R] {N r : ℕ} (A : Matrix (Fin N) (Fin N) R)
    (hA : A.det ≠ 0) :
    (Matrix.of (fun T S : {U : Finset (Fin N) // U.card = r} =>
      (A.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det)).det ≠ 0 := by
  have hcomp : compound r A * compound r A⁻¹ = 1 := by
    rw [← compound_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), compound_one]
  exact Matrix.det_ne_zero_of_right_inverse hcomp

end Commons.LinearAlgebra.Matrix