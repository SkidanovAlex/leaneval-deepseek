import Mathlib
import Submission.Commons.NumberTheory.NumberField.discr_adjoinRoot_cubic_bad6_eq

namespace Commons.Polynomial

theorem abs_discr_ge_23_of_adjoinRoot_cubic_bad6 (a b c : ℤ)
    (h : (a, b, c) ∈ [(-2,0,2), (-1,1,1), (-1,3,-1), (1,1,-1), (1,3,1), (2,0,-2)])
    [Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)))] :
    23 ≤ |NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)))| := by
  simp at h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hdiscQ : ((NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((-2 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((2 : ℤ) : ℚ))) : ℤ) : ℚ) = Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((-2 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((2 : ℤ) : ℚ)) := by
      exact @Commons.NumberTheory.NumberField.discr_adjoinRoot_cubic_bad6_eq (-2) (0) (2)
        (by simpa using (inferInstance : Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C ((-2 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((2 : ℤ) : ℚ))))) (by simp)
    have hpoly : Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((-2 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((2 : ℤ) : ℚ)) = (-44 : ℚ) := by
      rw [Polynomial.discr_of_degree_eq_three]
      · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_zero]
      · compute_degree <;> norm_num
    have hd : NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((-2 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((2 : ℤ) : ℚ))) = (-44 : ℤ) := by
      exact_mod_cast (hdiscQ.trans hpoly)
    norm_num [hd]
  · have hdiscQ : ((NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((-1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((1 : ℤ) : ℚ))) : ℤ) : ℚ) = Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((-1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((1 : ℤ) : ℚ)) := by
      exact @Commons.NumberTheory.NumberField.discr_adjoinRoot_cubic_bad6_eq (-1) (1) (1)
        (by simpa using (inferInstance : Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C ((-1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((1 : ℤ) : ℚ))))) (by simp)
    have hpoly : Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((-1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((1 : ℤ) : ℚ)) = (-44 : ℚ) := by
      rw [Polynomial.discr_of_degree_eq_three]
      · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_zero]
      · compute_degree <;> norm_num
    have hd : NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((-1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((1 : ℤ) : ℚ))) = (-44 : ℤ) := by
      exact_mod_cast (hdiscQ.trans hpoly)
    norm_num [hd]
  · have hdiscQ : ((NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((-1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-1 : ℤ) : ℚ))) : ℤ) : ℚ) = Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((-1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-1 : ℤ) : ℚ)) := by
      exact @Commons.NumberTheory.NumberField.discr_adjoinRoot_cubic_bad6_eq (-1) (3) (-1)
        (by simpa using (inferInstance : Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C ((-1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-1 : ℤ) : ℚ))))) (by simp)
    have hpoly : Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((-1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-1 : ℤ) : ℚ)) = (-76 : ℚ) := by
      rw [Polynomial.discr_of_degree_eq_three]
      · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_zero]
      · compute_degree <;> norm_num
    have hd : NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((-1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-1 : ℤ) : ℚ))) = (-76 : ℤ) := by
      exact_mod_cast (hdiscQ.trans hpoly)
    norm_num [hd]
  · have hdiscQ : ((NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-1 : ℤ) : ℚ))) : ℤ) : ℚ) = Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-1 : ℤ) : ℚ)) := by
      exact @Commons.NumberTheory.NumberField.discr_adjoinRoot_cubic_bad6_eq (1) (1) (-1)
        (by simpa using (inferInstance : Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-1 : ℤ) : ℚ))))) (by simp)
    have hpoly : Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-1 : ℤ) : ℚ)) = (-44 : ℚ) := by
      rw [Polynomial.discr_of_degree_eq_three]
      · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_zero]
      · compute_degree <;> norm_num
    have hd : NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-1 : ℤ) : ℚ))) = (-44 : ℤ) := by
      exact_mod_cast (hdiscQ.trans hpoly)
    norm_num [hd]
  · have hdiscQ : ((NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((1 : ℤ) : ℚ))) : ℤ) : ℚ) = Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((1 : ℤ) : ℚ)) := by
      exact @Commons.NumberTheory.NumberField.discr_adjoinRoot_cubic_bad6_eq (1) (3) (1)
        (by simpa using (inferInstance : Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((1 : ℤ) : ℚ))))) (by simp)
    have hpoly : Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((1 : ℤ) : ℚ)) = (-76 : ℚ) := by
      rw [Polynomial.discr_of_degree_eq_three]
      · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_zero]
      · compute_degree <;> norm_num
    have hd : NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((1 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((1 : ℤ) : ℚ))) = (-76 : ℤ) := by
      exact_mod_cast (hdiscQ.trans hpoly)
    norm_num [hd]
  · have hdiscQ : ((NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((2 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-2 : ℤ) : ℚ))) : ℤ) : ℚ) = Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((2 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-2 : ℤ) : ℚ)) := by
      exact @Commons.NumberTheory.NumberField.discr_adjoinRoot_cubic_bad6_eq (2) (0) (-2)
        (by simpa using (inferInstance : Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C ((2 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-2 : ℤ) : ℚ))))) (by simp)
    have hpoly : Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C ((2 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-2 : ℤ) : ℚ)) = (-44 : ℚ) := by
      rw [Polynomial.discr_of_degree_eq_three]
      · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_zero]
      · compute_degree <;> norm_num
    have hd : NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C ((2 : ℤ) : ℚ) * Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X + Polynomial.C ((-2 : ℤ) : ℚ))) = (-44 : ℤ) := by
      exact_mod_cast (hdiscQ.trans hpoly)
    norm_num [hd]

end Commons.Polynomial
