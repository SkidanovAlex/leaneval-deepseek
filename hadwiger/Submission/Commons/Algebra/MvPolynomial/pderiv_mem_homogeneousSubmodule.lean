import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

namespace Commons.Algebra.MvPolynomial

theorem pderiv_mem_homogeneousSubmodule
    {n : ℕ} (i : Fin n) {φ : MvPolynomial (Fin n) ℝ} {k : ℕ}
    (hφ : φ ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :
    MvPolynomial.pderiv i φ ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 1) := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact _root_.MvPolynomial.IsHomogeneous.pderiv
    (by rwa [MvPolynomial.mem_homogeneousSubmodule] at hφ)

end Commons.Algebra.MvPolynomial