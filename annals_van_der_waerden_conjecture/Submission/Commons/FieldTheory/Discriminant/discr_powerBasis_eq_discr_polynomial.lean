import Mathlib.NumberTheory.NumberField.Basic
import Submission.Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr

namespace Commons.FieldTheory.Discriminant

open Polynomial in
/-- **The discriminant of the power basis of `AdjoinRoot f` is the polynomial discriminant of
`f`.**

For a monic `f : ℚ[X]` with `AdjoinRoot f` a field, the discriminant of the power basis
`{1, gen, gen², …}` is `Polynomial.discr f`.

Proof: `Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr` identifies it with
`Polynomial.discr (minpoly ℚ pb.gen)`, and
`AdjoinRoot.minpoly_powerBasis_gen_of_monic` identifies `minpoly ℚ (AdjoinRoot.root f)` with `f`
(needs `[Algebra.IsSeparable ℚ (AdjoinRoot f)]`, automatic in characteristic `0`). -/
theorem discr_powerBasis_eq_discr_polynomial {f : Polynomial ℚ} (hf : f.Monic) (hf0 : f ≠ 0)
    [Fact (Irreducible f)] :
    Algebra.discr ℚ (AdjoinRoot.powerBasis hf0).basis = Polynomial.discr f := by
  have h := Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr
    (F := ℚ) (S := AdjoinRoot f) (pb := AdjoinRoot.powerBasis hf0)
  rw [AdjoinRoot.minpoly_powerBasis_gen hf0, hf.leadingCoeff] at h
  simp only [inv_one, Polynomial.C_1, mul_one] at h
  exact h.symm

end Commons.FieldTheory.Discriminant