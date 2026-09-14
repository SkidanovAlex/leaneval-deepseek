import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Submission.Commons.Lattice.Discrete.discreteTopology_of_le

set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Lattice.Finrank

theorem finrank_sup_add_finrank_inf_eq_of_discrete {n : ℕ}
    {L₀ L₁ L₂ : Submodule ℤ (EuclideanSpace ℝ (Fin n))} [DiscreteTopology L₀]
    (h₁ : L₁ ≤ L₀) (h₂ : L₂ ≤ L₀) :
    Module.finrank ℤ ↥(L₁ ⊔ L₂) + Module.finrank ℤ ↥(L₁ ⊓ L₂) =
      Module.finrank ℤ ↥L₁ + Module.finrank ℤ ↥L₂ := by
  classical
  -- each of L₁, L₂, L₁ ⊓ L₂ and L₁ ⊔ L₂ is a discrete submodule of the discrete lattice L₀,
  -- hence (by the ZLattice API) a finite free ℤ-module
  haveI d₁ : DiscreteTopology ↥L₁ :=
    Commons.Lattice.Discrete.discreteTopology_of_le (ℒ := L₀) (ℒ' := L₁) h₁
  haveI d₂ : DiscreteTopology ↥L₂ :=
    Commons.Lattice.Discrete.discreteTopology_of_le (ℒ := L₀) (ℒ' := L₂) h₂
  haveI d_inf : DiscreteTopology ↥(L₁ ⊓ L₂) :=
    Commons.Lattice.Discrete.discreteTopology_of_le (ℒ := L₀) (ℒ' := L₁ ⊓ L₂)
      (le_trans inf_le_left h₁)
  haveI d_sup : DiscreteTopology ↥(L₁ ⊔ L₂) :=
    Commons.Lattice.Discrete.discreteTopology_of_le (ℒ := L₀) (ℒ' := L₁ ⊔ L₂)
      (sup_le h₁ h₂)
  haveI f₁ : Module.Finite ℤ ↥L₁ := instModuleFinite_of_discrete_submodule L₁
  haveI f₂ : Module.Finite ℤ ↥L₂ := instModuleFinite_of_discrete_submodule L₂
  haveI f_inf : Module.Finite ℤ ↥(L₁ ⊓ L₂) := instModuleFinite_of_discrete_submodule (L₁ ⊓ L₂)
  haveI f_sup : Module.Finite ℤ ↥(L₁ ⊔ L₂) := instModuleFinite_of_discrete_submodule (L₁ ⊔ L₂)
  -- the rank formula for submodules holds at the level of `Module.rank` over any ring
  have hkey : Module.rank ℤ ↥(L₁ ⊔ L₂) + Module.rank ℤ ↥(L₁ ⊓ L₂) =
      Module.rank ℤ ↥L₁ + Module.rank ℤ ↥L₂ :=
    Submodule.rank_sup_add_rank_inf_eq L₁ L₂
  -- for finite modules `finrank` is the natural-number shadow of `Module.rank`
  rw [← Module.finrank_eq_rank (R := ℤ) (M := ↥(L₁ ⊔ L₂)),
      ← Module.finrank_eq_rank (R := ℤ) (M := ↥(L₁ ⊓ L₂)),
      ← Module.finrank_eq_rank (R := ℤ) (M := ↥L₁),
      ← Module.finrank_eq_rank (R := ℤ) (M := ↥L₂)] at hkey
  exact_mod_cast hkey

end Commons.Lattice.Finrank