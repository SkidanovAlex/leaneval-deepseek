import Mathlib.Algebra.Module.ZLattice.Covolume

namespace Commons.Lattice.Minkowski

theorem covolume_eq_of_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₁] [IsZLattice ℝ L₂] (h : L₁ = L₂) : ZLattice.covolume L₁ = ZLattice.covolume L₂ := by
  rw [h]

end Commons.Lattice.Minkowski