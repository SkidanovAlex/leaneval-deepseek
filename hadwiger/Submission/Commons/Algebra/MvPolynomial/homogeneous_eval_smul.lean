import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Commons.Algebra.MvPolynomial

/-- Scaling the variables of a homogeneous polynomial of degree `k` by a scalar `t`
multiplies the value by `t ^ k`. -/
theorem homogeneous_eval_smul
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) {k : ℕ}
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial.eval (fun i => (t • x : EuclideanSpace ℝ (Fin n)) i) P
      = t ^ k * MvPolynomial.eval (fun i => x i) P := by
  classical
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP
  have hfun : (fun i => (t • x : EuclideanSpace ℝ (Fin n)) i) = (fun i => t * x i) := by
    funext i; simp
  rw [hfun, MvPolynomial.eval_eq' (fun i : Fin n => t * x i) P,
    MvPolynomial.eval_eq' (fun i : Fin n => x i) P, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdne : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hdeg : d.degree = k := by
    by_contra h
    exact hdne (MvPolynomial.IsHomogeneous.coeff_eq_zero hP h)
  have hsum : (∑ i : Fin n, d i) = k := (Finsupp.degree_eq_sum d).symm.trans hdeg
  have hprod : (∏ i : Fin n, (t * x i) ^ (d i)) = t ^ k * (∏ i : Fin n, (x i) ^ (d i)) := by
    calc (∏ i : Fin n, (t * x i) ^ (d i))
        = ∏ i : Fin n, (t ^ (d i)) * (x i) ^ (d i) := by
            apply Finset.prod_congr rfl
            intro i _
            rw [mul_pow]
      _ = (∏ i : Fin n, t ^ (d i)) * (∏ i : Fin n, (x i) ^ (d i)) := by
            rw [Finset.prod_mul_distrib]
      _ = t ^ (∑ i : Fin n, d i) * (∏ i : Fin n, (x i) ^ (d i)) := by
            rw [Finset.prod_pow_eq_pow_sum]
      _ = t ^ k * (∏ i : Fin n, (x i) ^ (d i)) := by rw [hsum]
  rw [hprod]
  ring

end Commons.Algebra.MvPolynomial