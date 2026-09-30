import Mathlib
import Submission.Commons.Analysis.MomentCurve.transversality_det

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.MomentCurve

/-- The full family `Γ^{(1)}(t), …, Γ^{(k)}(t)` of derivative vectors of the moment curve is a
basis of `ℝ^k`: the matrix with these as columns is lower triangular with diagonal entries
`(i+1)! ≠ 0`. -/
theorem linearIndependent_gam_univ (k : ℕ) (t : ℝ) :
    LinearIndependent ℝ (fun i : Fin k => (fun j : Fin k => gam k t (i.val + 1) j)) := by
  set M : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.of (fun (j i : Fin k) => gam k t (i.val + 1) j) with hM
  have hlow : M.IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    show M i j = 0
    rw [hM, Matrix.of_apply, gam_apply]
    have h0 : (i.val + 1).descFactorial (j.val + 1) = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [h0, Nat.cast_zero, zero_mul]
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular M hlow, Finset.prod_ne_zero_iff]
    intro i _
    rw [hM, Matrix.of_apply, gam_apply, Nat.sub_self, pow_zero, mul_one, Nat.descFactorial_self]
    exact_mod_cast Nat.factorial_ne_zero (i.val + 1)
  have hunit : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  have hcol : LinearIndependent ℝ M.col := Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
  have hgoal : (fun i : Fin k => (fun j : Fin k => gam k t (i.val + 1) j)) = M.col := by
    funext i j
    rw [hM, Matrix.col_apply, Matrix.of_apply]
  rwa [hgoal]

theorem linearIndependent_gam (k m : ℕ) (hm : m ≤ k) (t : ℝ) :
    LinearIndependent ℝ (fun i : Fin m => (fun j : Fin k => gam k t (i.val + 1) j)) := by
  have h := (linearIndependent_gam_univ k t).comp (Fin.castLE hm) (Fin.castLE_injective hm)
  rw [show (fun i : Fin m => (fun j : Fin k => gam k t (i.val + 1) j))
      = ((fun i : Fin k => (fun j : Fin k => gam k t (i.val + 1) j)) ∘ Fin.castLE hm) from by
    funext i j
    simp only [Function.comp_apply, Fin.val_castLE]]
  exact h

end Commons.Analysis.MomentCurve
