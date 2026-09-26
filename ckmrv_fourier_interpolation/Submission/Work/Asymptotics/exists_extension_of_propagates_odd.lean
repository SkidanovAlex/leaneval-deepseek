import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.PropagateCarriesOdd
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Asymptotics.exists_Mp_nbdh
import Submission.Work.Asymptotics.defects_of_local_agreement
import Submission.Work.Asymptotics.exists_neighbour_nbdh_of_Propagates
import Submission.Work.Asymptotics.SmallExtensionOdd
import Submission.Work.Asymptotics.Fodd_well_defined

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

theorem exists_extension_of_propagates_odd {k : ℤ} (hk : Odd k) {O : Set UpperHalfPlane}
    {f h₁ h₂ : UpperHalfPlane → ℂ}
    (h : Work.Asymptotics.Propagates k O f h₁ h₂)
    (hO : closure Work.Asymptotics.DomainD ⊆ O) :
    ∃ F : UpperHalfPlane → ℂ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F ∧
      (∃ U : Set UpperHalfPlane, IsOpen U ∧ closure Work.Asymptotics.DomainD ⊆ U ∧ U ⊆ O ∧
        ∀ τ ∈ U, F τ = f τ) ∧
      (∀ τ : UpperHalfPlane, Work.Kernels.T2op F τ = h₁ τ) ∧
      (∀ τ : UpperHalfPlane, Work.Asymptotics.S2op k F τ = h₂ τ) := by
  have hOopen : IsOpen O := h.1
  have hh₁md : MDiff h₁ := h.2.1
  have hh₂md : MDiff h₂ := h.2.2.1
  have hfOn : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f O := h.2.2.2.1
  have hT := h.2.2.2.2.1
  have hS := h.2.2.2.2.2
  obtain ⟨O_F, hOp, hclF, hMpO, hNbd⟩ :=
    Work.Asymptotics.exists_neighbour_nbdh_of_Propagates hOopen hO
  have hwd : ∀ (γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ τ' : UpperHalfPlane),
      τ ∈ O_F → τ' ∈ O_F → γ • τ = γ' • τ' →
      Work.Kernels.jFun γ (τ : ℂ) ^ k * Work.Asymptotics.Psi k f h₁ h₂ γ τ
        = Work.Kernels.jFun γ' (τ' : ℂ) ^ k * Work.Asymptotics.Psi k f h₁ h₂ γ' τ' :=
    fun γ γ' τ τ' hτ hτ' hEq =>
      Work.Asymptotics.Fodd_well_defined hk hMpO hT hS hNbd hτ hτ' hEq
  let F : UpperHalfPlane → ℂ := Work.Asymptotics.Fodd O_F k f h₁ h₂
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F :=
    Work.Asymptotics.mdifferentiable_Fodd (O := O) hOp hclF hMpO hfOn hh₁md hh₂md hwd
  have hU : ∃ U : Set UpperHalfPlane, IsOpen U ∧ closure Work.Asymptotics.DomainD ⊆ U ∧
      U ⊆ O ∧ ∀ τ ∈ U, F τ = f τ := by
    refine ⟨⋃ i : Fin 6, (fun τ : UpperHalfPlane => (Work.Asymptotics.Mp i) • τ) '' O_F,
      Work.Asymptotics.isOpen_iUnion_Mp_smul hOp,
      Work.Asymptotics.closure_DomainD_subset_iUnion_Mp_smul hclF,
      Work.Asymptotics.iUnion_Mp_smul_subset hMpO, ?_⟩
    intro τ hτ
    rw [Set.mem_iUnion] at hτ
    obtain ⟨i, σ, hσ, rfl⟩ := hτ
    exact Work.Asymptotics.Fodd_Mp_eq (O := O) hk hwd i hσ
  obtain ⟨hd₁, hd₂⟩ := Work.Asymptotics.defects_of_local_agreement h hmd hU
  exact ⟨F, hmd, hU, hd₁, hd₂⟩

end Work.Asymptotics
