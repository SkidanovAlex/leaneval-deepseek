import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open MonoidHom

namespace Work.SSGRoute

/-- Topological core: if a homomorphism `ψ` is right-invariant under an open subgroup `U` of its source, its kernel is open. -/
theorem isOpen_ker_of_invariant_open_subgroup {Γ Q : Type*} [Group Γ] [Group Q]
    [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    (ψ : Γ →* Q) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    (hinv : ∀ σ u : Γ, u ∈ U → ψ (σ * u) = ψ σ) :
    IsOpen (ψ.ker : Set Γ) := by
  -- `U` consists of elements on which `ψ` is trivial, so `U ⊆ ker ψ`; consequently `ker ψ`
  -- is a union of left translates (cosets) of the open set `U`.
  have hker : (ψ.ker : Set Γ) = ⋃ g : ψ.ker, (g : Γ) • (U : Set Γ) := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      rw [Set.mem_smul_set]
      exact ⟨1, U.one_mem, mul_one x⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨g, hg⟩
      rw [Set.mem_smul_set] at hg
      rcases hg with ⟨u, hu, rfl⟩
      refine mem_ker.mpr ?_
      change ψ ((g : Γ) * u) = 1
      rw [hinv (g : Γ) u hu]
      exact mem_ker.mp g.2
  rw [hker]
  exact isOpen_iUnion fun g => hU.leftCoset (g : Γ)

end Work.SSGRoute
