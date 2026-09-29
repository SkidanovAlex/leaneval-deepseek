import Mathlib.Algebra.Polynomial.Div

namespace Commons.Algebra.Polynomial

/-- If the root multiplicities of two nonzero polynomials at `α` are different, then the
multiplicity of the sum is the smaller one. -/
theorem rootMultiplicity_add_eq_of_lt {K : Type*} [Field K] {α : K} {p q : Polynomial K}
    (hp : p ≠ 0) (h : Polynomial.rootMultiplicity α p < Polynomial.rootMultiplicity α q) :
    Polynomial.rootMultiplicity α (p + q) = Polynomial.rootMultiplicity α p := by
  classical
  -- `q ≠ 0`: otherwise `rootMultiplicity α q = 0`, contradicting `h`.
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [Polynomial.rootMultiplicity_zero] at h
    exact absurd h (not_lt.mpr (Nat.zero_le _))
  -- Translate the strict inequality of root multiplicities into one of `multiplicity`s.
  have hm : multiplicity (Polynomial.X - Polynomial.C α) p
      < multiplicity (Polynomial.X - Polynomial.C α) q := by
    have h' := h
    rw [Polynomial.rootMultiplicity_eq_multiplicity p α, if_neg hp,
      Polynomial.rootMultiplicity_eq_multiplicity q α, if_neg hq0] at h'
    exact h'
  -- `multiplicity` of a sum is the smaller one when the multiplicities differ.
  have hmain : multiplicity (Polynomial.X - Polynomial.C α) (q + p)
      = multiplicity (Polynomial.X - Polynomial.C α) p :=
    (Polynomial.finiteMultiplicity_X_sub_C α hp).multiplicity_add_of_gt hm
  -- `p + q ≠ 0`, since `p + q = 0` would force `rootMultiplicity α q = rootMultiplicity α p`.
  have hsum0 : p + q ≠ 0 := by
    intro hpq
    have hq_eq : q = -p := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hpq)
    rw [hq_eq, multiplicity_neg] at hm
    exact absurd hm (lt_irrefl _)
  -- Re-express both root multiplicities through `multiplicity`.
  rw [Polynomial.rootMultiplicity_eq_multiplicity (p + q) α, if_neg hsum0,
    Polynomial.rootMultiplicity_eq_multiplicity p α, if_neg hp, add_comm]
  exact hmain

end Commons.Algebra.Polynomial