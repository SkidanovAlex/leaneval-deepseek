import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Submission.Commons.Lattice.FundamentalDomain.submodule_toAddSubgroup_fundamentalDomain

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Lattice.Minkowski

open MeasureTheory
open scoped ENNReal

lemma euclidean_first_minimum_of_covolume_le
    {n : ℕ} (hE : Nontrivial (EuclideanSpace ℝ (Fin n)))
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    {R : ℝ} (hR : 0 ≤ R)
    (hvol : volume (ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L (Module.finBasis ℤ L))) *
        (2 : ℝ≥0∞) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) ≤
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
    ∃ v : L, v ≠ 0 ∧ ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ R := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let F : Set E := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L (Module.finBasis ℤ L))
  let L0 : AddSubgroup E := L.toAddSubgroup
  have hcount : Countable ↥L0 := by
    exact (inferInstance : Countable ↥L)
  have hdisc : DiscreteTopology ↥L0 := by
    exact (inferInstance : DiscreteTopology ↥L)
  letI : Countable ↥L0 := hcount
  letI : DiscreteTopology ↥L0 := hdisc
  have hfund : IsAddFundamentalDomain ↥L0 F volume := by
    dsimp [L0]
    exact Commons.Lattice.FundamentalDomain.submodule_toAddSubgroup_fundamentalDomain L
      (ZLattice.isAddFundamentalDomain (Module.finBasis ℤ L) volume)
  obtain ⟨x, hx0, hxmem⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (E := E) (μ := volume) (L := L0) (F := F)
      (s := Metric.closedBall (0 : E) R) hfund
      (by
        intro y hy
        rw [Metric.mem_closedBall] at hy ⊢
        simpa [dist_eq_norm] using hy)
      (convex_closedBall (0 : E) R)
      (ProperSpace.isCompact_closedBall (0 : E) R)
      hvol
  refine ⟨⟨x, ?_⟩, ?_, ?_⟩
  · exact x.2
  · exact hx0
  · have hnorm : dist (x : E) (0 : E) ≤ R := Metric.mem_closedBall.mp hxmem
    simpa [dist_eq_norm] using hnorm

end Commons.Lattice.Minkowski