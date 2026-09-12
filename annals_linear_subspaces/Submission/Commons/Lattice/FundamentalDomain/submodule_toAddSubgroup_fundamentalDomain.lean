import Mathlib.Algebra.Module.ZLattice.Basic

namespace Commons.Lattice.FundamentalDomain

open MeasureTheory

lemma submodule_toAddSubgroup_fundamentalDomain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {F : Set E} (hF : IsAddFundamentalDomain L F volume) :
    IsAddFundamentalDomain L.toAddSubgroup F volume := by
  exact hF

end Commons.Lattice.FundamentalDomain