import Mathlib
import Submission.Work.MotAS.AsRuleQAPhi
import Submission.Work.MotAS.AsRuleQASum

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Work.MotAS

open MvPolynomial Polynomial

variable {K : Type} [Field K] [CharP K 5]

private lemma natDegree_C_mul_le' {R : Type*} [Semiring R] (x : R) (f : Polynomial R) :
    (Polynomial.C x * f).natDegree ≤ f.natDegree := by
  calc (Polynomial.C x * f).natDegree ≤ (Polynomial.C x).natDegree + f.natDegree :=
        Polynomial.natDegree_mul_le
    _ = f.natDegree := by rw [Polynomial.natDegree_C, zero_add]

lemma asPhiP_coeff0 (a b g : K) : (asPhiP a b g).coeff 0 = asPhiP_c0 a b g := by
  simp only [asPhiP, asRterms, asPhiP_c0,
    asTriR1, asTriR2, asTriR3, asTriR4, asTriR5, asTriR6, asTriR7, asTriR8, asTriR9, asTriR10, asTriR11, asTriR12, asTriR13, asTriR14, asTriR15,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
    mul_zero, add_zero, zero_add]
  norm_num

lemma asPhiP_coeff1 (a b g : K) : (asPhiP a b g).coeff 1 = asPhiP_c1 a b g := by
  simp only [asPhiP, asRterms, asPhiP_c1,
    asTriR1, asTriR2, asTriR3, asTriR4, asTriR5, asTriR6, asTriR7, asTriR8, asTriR9, asTriR10, asTriR11, asTriR12, asTriR13, asTriR14, asTriR15,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
    mul_zero, add_zero, zero_add]
  norm_num

lemma asPhiP_coeff2 (a b g : K) : (asPhiP a b g).coeff 2 = asPhiP_c2 a b g := by
  simp only [asPhiP, asRterms, asPhiP_c2,
    asTriR1, asTriR2, asTriR3, asTriR4, asTriR5, asTriR6, asTriR7, asTriR8, asTriR9, asTriR10, asTriR11, asTriR12, asTriR13, asTriR14, asTriR15,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
    mul_zero, add_zero, zero_add]
  norm_num

lemma asPhiP_coeff3 (a b g : K) : (asPhiP a b g).coeff 3 = asPhiP_c3 a b g := by
  simp only [asPhiP, asRterms, asPhiP_c3,
    asTriR1, asTriR2, asTriR3, asTriR4, asTriR5, asTriR6, asTriR7, asTriR8, asTriR9, asTriR10, asTriR11, asTriR12, asTriR13, asTriR14, asTriR15,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
    mul_zero, add_zero, zero_add]
  norm_num

lemma asPhiP_coeff4 (a b g : K) : (asPhiP a b g).coeff 4 = asPhiP_c4 a b g := by
  simp only [asPhiP, asRterms, asPhiP_c4,
    asTriR1, asTriR2, asTriR3, asTriR4, asTriR5, asTriR6, asTriR7, asTriR8, asTriR9, asTriR10, asTriR11, asTriR12, asTriR13, asTriR14, asTriR15,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
    mul_zero, add_zero, zero_add]
  norm_num

lemma asPhiP_natDegree (a b g : K) : (asPhiP a b g).natDegree ≤ 4 := by
  rw [asPhiP, asRterms]
  have h1 : (Polynomial.C (asCt1 a b g) * asTriR1 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR1]; compute_degree)
  have h2 : (Polynomial.C (asCt2 a b g) * asTriR2 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR2]; compute_degree)
  have h3 : (Polynomial.C (asCt3 a b g) * asTriR3 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR3]; compute_degree)
  have h4 : (Polynomial.C (asCt4 a b g) * asTriR4 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR4]; compute_degree)
  have h5 : (Polynomial.C (asCt5 a b g) * asTriR5 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR5]; compute_degree)
  have h6 : (Polynomial.C (asCt6 a b g) * asTriR6 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR6]; compute_degree)
  have h7 : (Polynomial.C (asCt7 a b g) * asTriR7 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR7]; compute_degree)
  have h8 : (Polynomial.C (asCt8 a b g) * asTriR8 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR8]; compute_degree)
  have h9 : (Polynomial.C (asCt9 a b g) * asTriR9 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR9]; compute_degree)
  have h10 : (Polynomial.C (asCt10 a b g) * asTriR10 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR10]; compute_degree)
  have h11 : (Polynomial.C (asCt11 a b g) * asTriR11 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR11]; compute_degree)
  have h12 : (Polynomial.C (asCt12 a b g) * asTriR12 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR12]; compute_degree)
  have h13 : (Polynomial.C (asCt13 a b g) * asTriR13 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR13]; compute_degree)
  have h14 : (Polynomial.C (asCt14 a b g) * asTriR14 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR14]; compute_degree)
  have h15 : (Polynomial.C (asCt15 a b g) * asTriR15 a b g).natDegree ≤ 4 :=
    le_trans (natDegree_C_mul_le' _ _) (by rw [asTriR15]; compute_degree)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h1 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h2 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h3 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h4 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h5 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h6 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h7 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h8 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h9 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h10 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h11 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h12 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h13 ?_)
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h14 ?_)
  exact h15

end Work.MotAS
