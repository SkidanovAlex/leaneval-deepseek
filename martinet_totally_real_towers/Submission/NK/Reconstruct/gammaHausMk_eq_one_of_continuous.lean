import Mathlib
import Submission.NK.Reconstruct.gammaHaus

namespace NK.Reconstruct

theorem gammaHausMk_eq_one_of_continuous {K K' K₂ K₂' : Type*}
    [Field K] [Field K'] [Algebra K K'] [IsGalois K K'] [Field K₂] [Field K₂'] [Algebra K₂ K₂']
    [IsGalois K₂ K₂'] (ℓ : ℕ) [Fact ℓ.Prime] (φ : NK.Reconstruct.Gamma K K' ℓ →*
      NK.Reconstruct.Gamma K₂ K₂' ℓ)
    (hφ : Continuous ⇑φ) {z : NK.Reconstruct.Gamma K K' ℓ}
    (hz : NK.Reconstruct.gammaHausMk (K := K) (K' := K') ℓ z = 1) :
    NK.Reconstruct.gammaHausMk (K := K₂) (K' := K₂') ℓ (φ z) = 1 := by
  have h := gammaHausLift_comp (K₁ := K) (K₁' := K') (K₂ := K₂) (K₂' := K₂') ℓ φ hφ z
  rw [hz, map_one] at h
  exact h.symm

end NK.Reconstruct
