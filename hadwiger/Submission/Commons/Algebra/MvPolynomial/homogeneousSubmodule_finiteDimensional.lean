import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Commons.Algebra.MvPolynomial

theorem homogeneousSubmodule_finiteDimensional {n : ℕ} {k : ℕ} :
    Module.Finite ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) := by
  classical
  exact (Module.Finite.iff_fg (R := ℝ) (M := MvPolynomial (Fin n) ℝ)
    (N := MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)).mpr
    (MvPolynomial.homogeneousSubmodule_fg (Fin n) ℝ k)

end Commons.Algebra.MvPolynomial