import Mathlib

namespace Work.FIArea5.HeckeZFR.Hadm

/-- If `Θ` and `ψ` are meromorphic on `U` and `Θ z = z ^ k * ψ z` for all `z`, then away from the
origin (where `z ^ k` is nonzero and analytic) the two functions have the same divisor on `U`. -/
theorem divisorFactorAway {Θ ψ : ℂ → ℂ} {U : Set ℂ} {k : ℕ}
    (hΘ : MeromorphicOn Θ U) (hψ : MeromorphicOn ψ U)
    (hfac : ∀ z : ℂ, Θ z = z ^ k * ψ z) {u : ℂ} (hu : u ≠ 0) :
    (MeromorphicOn.divisor Θ U) u = (MeromorphicOn.divisor ψ U) u := by
  by_cases huU : u ∈ U
  · rw [MeromorphicOn.divisor_apply hΘ huU, MeromorphicOn.divisor_apply hψ huU]
    congr 1
    have hker : Θ = (fun z : ℂ => z ^ k) * ψ := by
      funext z; exact hfac z
    rw [hker,
      meromorphicOrderAt_mul_of_ne_zero (g := fun z : ℂ => z ^ k) (by fun_prop)
        (by simpa using pow_ne_zero k hu)]
  · rw [MeromorphicOn.divisor_def, MeromorphicOn.divisor_def]
    simp [huU]

end Work.FIArea5.HeckeZFR.Hadm
