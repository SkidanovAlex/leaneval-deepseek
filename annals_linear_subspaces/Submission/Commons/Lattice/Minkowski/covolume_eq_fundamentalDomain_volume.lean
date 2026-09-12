import Mathlib.Algebra.Module.ZLattice.Covolume

namespace Commons.Lattice.Minkowski

open MeasureTheory
open scoped ENNReal

lemma covolume_eq_fundamentalDomain_volume
    {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L] :
    ENNReal.ofReal (ZLattice.covolume L) =
      volume (ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L (Module.finBasis ℤ L))) := by
  classical
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (L := L) (μ := volume)
        (ZLattice.isAddFundamentalDomain (Module.finBasis ℤ L) volume)]
  rw [measureReal_def]
  exact ENNReal.ofReal_toReal (ne_of_lt (Bornology.IsBounded.measure_lt_top
    (ZSpan.fundamentalDomain_isBounded (Module.Basis.ofZLatticeBasis ℝ L (Module.finBasis ℤ L)))))

end Commons.Lattice.Minkowski
