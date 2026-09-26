import Mathlib

namespace Work.Smooth.Morse.MorseModel

/-- An injective continuous linear map out of `ℂ` (viewed as a finite-dimensional real
vector space) is bounded below by a positive constant. -/
theorem exists_lower_bound_of_injective {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : ℂ →L[ℝ] F} (hA : Function.Injective A) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ, c * ‖v‖ ≤ ‖A v‖ := by
  have hEmb : Topology.IsEmbedding (A : ℂ → F) := by
    have hker : (A : ℂ →ₗ[ℝ] F).ker = ⊥ := LinearMap.ker_eq_bot.mpr hA
    exact (LinearMap.isClosedEmbedding_of_injective hker).isEmbedding
  have h : ∃ K, AntilipschitzWith K ⇑A :=
    ContinuousLinearMap.antilipschitz_of_isEmbedding A hEmb
  exact (antilipschitzWith_iff_exists_mul_le_norm (f := A)).mp h

end Work.Smooth.Morse.MorseModel
