import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Conjugating a function that is locally constant on `H` (with respect to an open subgroup of
`Γ`) by an element `σ` that normalises `H` into itself again gives a function locally constant
on `H`: the witnessing open subgroup is transported by the conjugation automorphism
`n ↦ σ⁻¹ * n * σ`. -/
theorem isLocConstOn_conj {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] {H : Subgroup Γ} {f : Γ → M} (hf : SSGRoute.IsLocConstOn H f) (σ : Γ)
    (hσ : ∀ n ∈ H, σ⁻¹ * n * σ ∈ H) :
    SSGRoute.IsLocConstOn H (fun n => f (σ⁻¹ * n * σ)) := by
  obtain ⟨U, hU, hfU⟩ := hf
  -- witness: conjugate the open subgroup `U` by `σ`; its elements are those `u` with
  -- `σ⁻¹ * u * σ ∈ U`.
  refine ⟨U.comap (MulAut.conj σ⁻¹).toMonoidHom, ?_, ?_⟩
  · exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · intro g hg u hu huH
    have hmem : σ⁻¹ * u * σ ∈ U := by simpa using hu
    have hg' : σ⁻¹ * g * σ ∈ H := hσ g hg
    have huH' : σ⁻¹ * u * σ ∈ H := hσ u huH
    have hgu : σ⁻¹ * (g * u) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * u * σ) := by group
    show f (σ⁻¹ * (g * u) * σ) = f (σ⁻¹ * g * σ)
    rw [hgu]
    exact hfU _ hg' _ hmem huH'

end Work.SSGRoute
