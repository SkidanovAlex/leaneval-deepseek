import Mathlib.Topology.Defs.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

theorem isLocConstOn_of_eq_hom_on_subgroup {Γ M : Type} [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] (H : Subgroup Γ) (f0 : ↥H →* Multiplicative M) (U : Subgroup Γ)
    (hU : IsOpen (U : Set Γ)) (hker : U.comap (Subgroup.subtype H) ≤ f0.ker) (f : Γ → M)
    (hf : ∀ (σ : Γ) (hσ : σ ∈ H), f σ = (f0 ⟨σ, hσ⟩).toAdd) :
    SSGRoute.IsLocConstOn H f := by
  refine ⟨U, hU, ?_⟩
  intro g hg u hu huH
  have hgu : g * u ∈ H := H.mul_mem hg huH
  rw [hf (g * u) hgu, hf g hg]
  have hmem : (⟨u, huH⟩ : ↥H) ∈ Subgroup.comap (Subgroup.subtype H) U := hu
  have hk : f0 ⟨u, huH⟩ = 1 := MonoidHom.mem_ker.mp (hker hmem)
  have hsplit : (⟨g * u, hgu⟩ : ↥H) = ⟨g, hg⟩ * ⟨u, huH⟩ := by ext; rfl
  rw [hsplit, map_mul, hk, mul_one]

end Work.SSGRoute
