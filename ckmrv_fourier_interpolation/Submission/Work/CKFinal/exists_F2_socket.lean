import Mathlib
import Submission.Work.LayerCont.LayerT2
import Submission.Work.LayerCont.FirstRecurrence
import Submission.Work.LayerCont.Glue.All
import Submission.Work.LayerCont.GlueBasic
import Submission.Work.LayerCont.InteriorDD.Cleanliness
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.Asymptotics.exists_pair_of_propagated_F2
import Submission.Work.CKFinal.Socket.Construction
import Submission.Work.CKFinal.Socket.F2_T2op
import Submission.Work.CKFinal.Socket.F2_agree_U0
import Submission.Work.CKFinal.Socket.F2_mdiff_O
import Submission.Work.CKFinal.Socket.F2_even
import Submission.Work.CKFinal.Socket.F2_S2op_main
import Submission.Work.CKFinal.Socket.closure_subset_O
import Submission.Work.CKFinal.Socket.paperLayer_U0_holo

namespace Work.CKFinal

/-- CKMRV Proposition 4.6 in the form consumed by `exists_extension_of_propagates`: one open
`O ⊇ closure 𝒟`, independent of `r`, and a family `F₂ r` holomorphic on `O`, equal to
`paperLayer` on `𝒟`, even in `r`, with the two recurrence defects of Corollary 5.2. -/
theorem exists_F2_socket (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ (O : Set UpperHalfPlane) (F₂ : ℝ → UpperHalfPlane → ℂ),
      IsOpen O ∧ closure Work.Asymptotics.DomainD ⊆ O ∧
      (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (F₂ r) O) ∧
      (∀ (r : ℝ) (τ : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD →
        F₂ r τ = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) ∧
      (∀ (r : ℝ) (τ : UpperHalfPlane), F₂ (-r) τ = F₂ r τ) ∧
      (∀ (r : ℝ) (τ : UpperHalfPlane), τ ∈ O → (1 : ℝ) +ᵥ τ ∈ O → (2 : ℝ) +ᵥ τ ∈ O →
        Work.Kernels.T2op (F₂ r) τ
          = -Work.Kernels.T2op (fun σ => Work.Kernels.gaussTerm σ r) τ) ∧
      (∀ (r : ℝ) (τ : UpperHalfPlane), ModularGroup.S • τ ∈ O →
        ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ O → ModularGroup.S • ((2 : ℝ) +ᵥ τ) ∈ O →
        Work.Asymptotics.S2op ((d : ℤ) / 2) (F₂ r) τ = 0) := by
  classical
  refine ⟨Socket.O ℓ d hd, fun r => Socket.F2 ℓ d hd r, Socket.isOpen_O ℓ d hd,
    Socket.closure_subset_O ℓ d hd, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact Socket.F2_mdiff_O ℓ d hd r (Socket.paperLayer_U0_holo ℓ d hd r)
  · intro r τ hτ
    exact Socket.F2_agree_U0 ℓ d hd r (Socket.DomainD_subset_U0 hτ)
  · intro r τ
    exact Socket.F2_even ℓ d hd r τ
  · intro r τ h1 h2 h3
    exact Socket.F2_T2op ℓ d hd r h1 h2 h3
  · intro r τ h1 h2 h3
    exact Socket.F2_S2op_main ℓ d hd r (Socket.paperLayer_U0_holo ℓ d hd r) h1 h2 h3

end Work.CKFinal
