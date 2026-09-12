import Mathlib
import Submission.Commons.Analysis.MeasureTheory.zonal_fibre_integral

namespace Commons.Analysis.MeasureTheory

theorem zonal_fibre_integral_abs_poly
    {n : ℕ} (i : Fin n) (hn : 2 ≤ n) (q : Polynomial ℝ) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        |(θ : EuclideanSpace ℝ (Fin n)) i| * Polynomial.eval ((θ : EuclideanSpace ℝ (Fin n)) i) q
      ∂MeasureTheory.volume.toSphere) =
    ∫ t : ℝ in Set.Ioo (-1) 1,
      (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) 1,
          (|t| * Polynomial.eval t q) *
            (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ i} : ℝ) - 2) / 2)
        ∂MeasureTheory.volume.toSphere) := by
  simpa using zonal_fibre_integral (n := n) i hn (fun t : ℝ => |t| * Polynomial.eval t q)

end Commons.Analysis.MeasureTheory
