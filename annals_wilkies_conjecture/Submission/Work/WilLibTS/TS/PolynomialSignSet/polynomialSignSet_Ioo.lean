import Mathlib
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite

namespace Work.WilLibTS.TS.PolynomialSignSet

/-- A box `{x | ∀ i, a i < x i ∧ x i < b i}` in the coordinates `id` is a
polynomial sign set: each coordinate constraint `a i < x i` resp. `x i < b i`
is the positivity of the polynomial `X i - C (a i)` resp. `C (b i) - X i`. -/
theorem polynomialSignSet_Ioo {ι : Type*} [Finite ι] (a b : ι → ℝ) :
    Work.WilLibTS.TS.PolynomialSignSet (id : (ι → ℝ) → ι → ℝ)
      {x : ι → ℝ | ∀ i, a i < x i ∧ x i < b i} := by
  classical
  apply PolynomialSignSet.forall_finite
  intro i
  have h1 : Work.WilLibTS.TS.PolynomialSignSet (id : (ι → ℝ) → ι → ℝ)
      {x : ι → ℝ | a i < x i} := by
    convert PolynomialSignSet.positive (c := (id : (ι → ℝ) → ι → ℝ))
      (MvPolynomial.X i - MvPolynomial.C (a i)) using 1
    ext x
    simp only [Set.mem_ofPred_eq, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
      sub_pos]
    rfl
  have h2 : Work.WilLibTS.TS.PolynomialSignSet (id : (ι → ℝ) → ι → ℝ)
      {x : ι → ℝ | x i < b i} := by
    convert PolynomialSignSet.positive (c := (id : (ι → ℝ) → ι → ℝ))
      (MvPolynomial.C (b i) - MvPolynomial.X i) using 1
    ext x
    simp only [Set.mem_ofPred_eq, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
      sub_pos]
    rfl
  exact h1.inter h2

end Work.WilLibTS.TS.PolynomialSignSet
