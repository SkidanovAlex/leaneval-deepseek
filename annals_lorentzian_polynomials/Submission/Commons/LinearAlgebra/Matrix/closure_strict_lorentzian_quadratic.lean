import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.closure_strict_lorentzian_quadratic_core

namespace Commons.LinearAlgebra.Matrix

open Matrix Polynomial Set Topology

theorem closure_strict_lorentzian_quadratic (n : ℕ) (hn : 0 < n) :
  closure {A : Matrix (Fin n) (Fin n) ℝ |
    A.IsSymm ∧ (∀ i j, 0 < A i j) ∧ IsUnit A ∧
      (A.charpoly.roots.filter (fun r => 0 < r)).card = 1} =
  {A : Matrix (Fin n) (Fin n) ℝ |
    A.IsSymm ∧ (∀ i j, 0 ≤ A i j) ∧
      (A.charpoly.roots.filter (fun r => 0 < r)).card ≤ 1} := by
  exact closure_strict_lorentzian_quadratic_core n hn

end Commons.LinearAlgebra.Matrix
