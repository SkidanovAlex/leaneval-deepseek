import Mathlib

/-!
# Covolume monotonicity under sublattice inclusion (shared commons)

If `L₁ ≤ L₂` are two full `ℤ`-lattices in the same ambient finite-dimensional real inner
product space, then `L₂` is the coarser lattice, so its covolume is no larger:
`covolume L₂ ≤ covolume L₁` (`covolume_le_covolume_of_le`).  This is the index/covolume
comparison used in geometry of numbers (e.g. the Hadamard side of Minkowski's second theorem:
`covol(L) ≤ covol(L₀) = ‖v₁∧…∧vₙ‖` for `L₀ = ℤ-span(v) ⊆ L`).

Proof: `ZLattice.covolume_div_covolume_eq_relIndex'` gives
`covolume L₁ / covolume L₂ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup` (a natural number);
positivity of both covolumes (`ZLattice.covolume_pos`) forces the relative index to be at
least `1`, hence `covolume L₂ ≤ covolume L₁`.

Mathlib-only.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Module
set_option autoImplicit false

namespace Commons.Lattice.Minkowski

-- covolume of a sublattice is at least the covolume of the ambient lattice:
-- L₁ ≤ L₂ ⟹ covol L₂ ≤ covol L₁
theorem covolume_le_covolume_of_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₂ ≤ ZLattice.covolume L₁ := by
  classical
  have hdiv : ZLattice.covolume L₁ / ZLattice.covolume L₂ =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    exact ZLattice.covolume_div_covolume_eq_relIndex' L₁ L₂ h
  have hrel1 : (1 : ℝ) ≤ (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    have hdivpos : 0 < ZLattice.covolume L₁ / ZLattice.covolume L₂ := by
      exact div_pos (ZLattice.covolume_pos L₁ volume) (ZLattice.covolume_pos L₂ volume)
    have hrelpos : 0 < (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
      rwa [hdiv] at hdivpos
    have hri0 : 0 < L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by exact_mod_cast hrelpos
    have hri : 1 ≤ L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by omega
    exact_mod_cast hri
  have hge : (1 : ℝ) ≤ ZLattice.covolume L₁ / ZLattice.covolume L₂ := by rwa [hdiv]
  have hcov2pos : 0 < ZLattice.covolume L₂ := ZLattice.covolume_pos L₂ volume
  have hmul := (le_div_iff₀ hcov2pos).mp hge
  -- hmul : 1 * covol L₂ ≤ covol L₁
  simpa using hmul
end Commons.Lattice.Minkowski
