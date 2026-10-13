import Mathlib

namespace Work.WilC4aRW.LinEquiv

theorem exists_pi_equiv {K : Type*} [Semiring K] {N : ℕ} (σ : Fin N ≃ Fin N) :
    ∃ P : (Fin N → K) ≃ₗ[K] (Fin N → K), ∀ x i, P x i = x (σ i) := by
  exact ⟨LinearEquiv.funCongrLeft K K σ, fun _ _ => rfl⟩

end Work.WilC4aRW.LinEquiv
