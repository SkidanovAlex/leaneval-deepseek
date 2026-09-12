import Mathlib
import Submission.Commons.Analysis.MeasureTheory.sphere_integral_sq_pos_of_homogeneous_nz

namespace Commons.Analysis.MeasureTheory

theorem sphere_restriction_pairing_pos
    {n : ℕ} [Nonempty (Fin n)] {k : ℕ}
    (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hPne : P ≠ 0) :
    0 < (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) P)^2
      ∂MeasureTheory.volume.toSphere) :=
  sphere_integral_sq_pos_of_homogeneous_nz (n := n) (k := k) P hP hPne

end Commons.Analysis.MeasureTheory
