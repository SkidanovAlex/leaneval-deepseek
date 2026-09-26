import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.fd_subset_DomainD
import Submission.Work.Asymptotics.closure_DomainD_subset_iUnion_Mp

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- Every point of the upper half plane is carried into the closure of the standard fundamental
domain `𝓕` by some element of `SL(2,ℤ)`. -/
theorem upperHalfPlane_subset_iUnion_smul_closure_DomainF :
    (Set.univ : Set UpperHalfPlane) ⊆
      ⋃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        (fun τ : UpperHalfPlane => γ • τ) '' (closure Work.Asymptotics.DomainF) := by
  intro τ _
  -- Mathlib's reduction into the standard fundamental domain `𝒟 = ModularGroup.fd`
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  have hgD : g • τ ∈ closure DomainD := subset_closure (fd_subset_DomainD hg)
  -- the six translates of `𝓕` cover `closure DomainD`
  have hcov : g • τ ∈ ⋃ i : Fin 6, (fun τ : UpperHalfPlane => (Mp i) • τ) '' closure DomainF :=
    closure_DomainD_subset_iUnion_Mp hgD
  rw [Set.mem_iUnion] at hcov
  obtain ⟨i, hi⟩ := hcov
  rw [Set.mem_image] at hi
  obtain ⟨x, hx, hxeq⟩ := hi
  have hx' : x = (Mp i)⁻¹ • (g • τ) := by rw [← hxeq, inv_smul_smul]
  rw [Set.mem_iUnion]
  refine ⟨((Mp i)⁻¹ * g)⁻¹, ?_⟩
  rw [Set.mem_image]
  refine ⟨(Mp i)⁻¹ • (g • τ), hx' ▸ hx, ?_⟩
  have hy : (Mp i)⁻¹ • (g • τ) = ((Mp i)⁻¹ * g) • τ := by rw [smul_smul]
  rw [hy, inv_smul_smul]

end Work.Asymptotics
