import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

namespace Commons.Algebra.MvPolynomial

theorem lap_mem_homogeneousSubmodule
    {n : ℕ} {φ : MvPolynomial (Fin n) ℝ} {k : ℕ}
    (hφ : φ ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :
    (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i φ)) ∈
      MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2) := by
  refine (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2)).sum_mem ?_
  intro i hi
  rw [MvPolynomial.mem_homogeneousSubmodule] at hφ ⊢
  have h1 : (MvPolynomial.pderiv i φ).IsHomogeneous (k - 1) :=
    MvPolynomial.IsHomogeneous.pderiv hφ
  have h2 : (MvPolynomial.pderiv i (MvPolynomial.pderiv i φ)).IsHomogeneous ((k - 1) - 1) :=
    MvPolynomial.IsHomogeneous.pderiv h1
  have hsub : (k - 1) - 1 = k - 2 := by omega
  simpa [hsub] using h2

end Commons.Algebra.MvPolynomial