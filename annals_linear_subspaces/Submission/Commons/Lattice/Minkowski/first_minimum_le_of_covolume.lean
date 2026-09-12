import Mathlib
import Submission.Commons.Lattice.Minkowski.euclidean_first_minimum_of_covolume_le
import Submission.Commons.Lattice.Minkowski.covolume_eq_fundamentalDomain_volume

namespace Commons.Lattice.Minkowski

open MeasureTheory
open scoped ENNReal

lemma first_minimum_le_of_covolume
    {n : ℕ} (hE : Nontrivial (EuclideanSpace ℝ (Fin n)))
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    {R : ℝ} (hR : 0 ≤ R)
    (hvol : ENNReal.ofReal (ZLattice.covolume L) *
        (2 : ℝ≥0∞) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) ≤
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
    ∃ v : L, v ≠ 0 ∧ ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ R := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let F : Set E := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L (Module.finBasis ℤ L))
  have hcov : ENNReal.ofReal (ZLattice.covolume L) = volume F := by
    simpa [F] using covolume_eq_fundamentalDomain_volume (L := L)
  have hvol' : volume F * (2 : ℝ≥0∞) ^ Module.finrank ℝ E ≤
      volume (Metric.closedBall (0 : E) R) := by
    rw [hcov] at hvol
    simpa [E] using hvol
  exact euclidean_first_minimum_of_covolume_le (n := n) (hE := hE) (L := L)
    (R := R) (hR := hR) (by simpa [E, F] using hvol')

end Commons.Lattice.Minkowski
