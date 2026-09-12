import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.RingTheory.TotallySplit

namespace Commons.Algebra.Module.ZLattice

theorem finiteIndex_comap_of_range_le
    {d : ℕ} {e : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℝ)}
    (he : Function.Injective e)
    {L : Submodule ℤ (Fin d → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≤ LinearMap.range e) :
    (L.comap e).toAddSubgroup.FiniteIndex := by
  let M : Submodule ℤ (Fin d → ℤ) := L.comap e
  have hfinrank : Module.finrank ℤ M = Module.finrank ℤ (Fin d → ℤ) := by
    calc
      Module.finrank ℤ M = Module.finrank ℤ L := by
        exact LinearEquiv.finrank_eq (Submodule.comap_equiv_self_of_inj_of_le he hL)
      _ = Module.finrank ℝ (Fin d → ℝ) := by
        exact ZLattice.rank ℝ L
      _ = Module.finrank ℤ (Fin d → ℤ) := by
        simp [Module.finrank_fintype_fun_eq_card]
  have hfin : Finite ((Fin d → ℤ) ⧸ M) := by
    exact Submodule.finiteQuotientOfFreeOfRankEq M hfinrank
  have hfin_add : Finite ((Fin d → ℤ) ⧸ M.toAddSubgroup) := hfin
  exact AddSubgroup.finiteIndex_of_finite_quotient

end Commons.Algebra.Module.ZLattice