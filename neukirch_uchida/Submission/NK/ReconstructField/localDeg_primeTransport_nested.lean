import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.Reconstruct.Transport
import Submission.NK.ReconstructField.localDegree_primeTransport

namespace NK.ReconstructField

/-- **The local degree is invariant under an isomorphism of the two extensions, in the nested
form.**  If `σ : L₂ ≃+* M₂` is compatible with `τ : L₁ ≃+* M₁` and `Q` lies over `P`, then the
local degree of `Q` over `P` equals that of the transported primes. -/
theorem localDeg_primeTransport_nested {L₁ L₂ M₁ M₂ : Type*} [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂] [Field M₁] [NumberField M₁] [Field M₂] [NumberField M₂]
    [Algebra L₁ L₂] [Algebra M₁ M₂] (σ : L₂ ≃+* M₂) (τ : L₁ ≃+* M₁)
    (hσ : ∀ x : L₁, σ (algebraMap L₁ L₂ x) = algebraMap M₁ M₂ (τ x))
    (Q : NK.Chebotarev.PrimeIdeal L₂) (P : NK.Chebotarev.PrimeIdeal L₁)
    (hQ : Q.asIdeal.LiesOver P.asIdeal) :
    NK.UchidaKummer.localDeg (NK.Reconstruct.primeTransport σ Q)
        (NK.Reconstruct.primeTransport τ P) = NK.UchidaKummer.localDeg Q P := by
  have h := localDegree_primeTransport (A₁ := L₁) (A₂ := M₁) (B₁ := L₂) (B₂ := M₂)
    σ τ hσ Q P hQ
  rw [NK.UchidaKummer.localDeg, NK.UchidaKummer.localDeg]
  exact h.symm

end NK.ReconstructField
