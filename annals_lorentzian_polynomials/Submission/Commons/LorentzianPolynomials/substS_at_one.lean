import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable

namespace Commons.LorentzianPolynomials

open Finsupp MvPolynomial BigOperators
set_option autoImplicit false

/-- `S(1,f) = f(1,…,1) · (Σ Xᵢ)^d`. -/
theorem substS_at_one (n d : ℕ) (f : Commons.LorentzianPolynomials.H n d) :
    MvPolynomial.aeval (fun j : Fin n => (∑ i : Fin n, MvPolynomial.X i)) f.1 =
      (MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) f.1 : ℝ) •
        ((∑ i : Fin n, MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ d) := by
  classical
  set S : MvPolynomial (Fin n) ℝ := ∑ i : Fin n, MvPolynomial.X i
  set φ : MvPolynomial (Fin n) ℝ := f.1 with hφdef
  have hφ : φ.IsHomogeneous d := by
    rw [hφdef]
    exact (MvPolynomial.mem_homogeneousSubmodule d f.1).mp f.2
  have hS : (MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) φ : ℝ) = ∑ x ∈ φ.support, φ.coeff x := by
    rw [MvPolynomial.eval_eq]
    simp
  calc
    MvPolynomial.aeval (fun _ : Fin n => S) φ = ∑ x ∈ φ.support, MvPolynomial.aeval (fun _ : Fin n => S) (MvPolynomial.monomial x (φ.coeff x)) := by
      conv_lhs => rw [φ.as_sum, MvPolynomial.aeval_sum]
    _ = ∑ x ∈ φ.support, (φ.coeff x) • (S ^ d) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxsum : (∑ i ∈ x.support, x i) = d := (hφ.degree_eq_sum_deg_support hx).symm
      rw [MvPolynomial.aeval_monomial]
      rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum]
      rw [hxsum]
      rw [MvPolynomial.algebraMap_eq]
      rw [← smul_eq_C_mul]
    _ = (∑ x ∈ φ.support, φ.coeff x) • (S ^ d) := by
      rw [Finset.sum_smul]
    _ = (MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) φ : ℝ) • (S ^ d) := by
      rw [hS]

end Commons.LorentzianPolynomials