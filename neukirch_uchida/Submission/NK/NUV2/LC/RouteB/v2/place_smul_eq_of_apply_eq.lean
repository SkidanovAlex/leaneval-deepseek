import Mathlib
import Submission.NK.GlobalCFT.Place

namespace NK.NUV2.LC.RouteB.v2

/-- The action of `Gal(E/K)` on the places of `E` (for the two different base fields `K`, `K'`)
depends only on the underlying function of the automorphism. -/
theorem place_smul_eq_of_apply_eq {K K' E : Type} [Field K] [NumberField K] [Field K']
    [NumberField K'] [Field E] [NumberField E] [Algebra K E] [Algebra K' E]
    (σ : E ≃ₐ[K] E) (τ : E ≃ₐ[K'] E) (h : ∀ x : E, σ x = τ x)
    (w : NK.GlobalCFT.Place E) :
    σ • w = τ • w := by
  -- The two automorphisms have the same inverse as functions as well.
  have hsymm : ∀ y : E, σ.symm y = τ.symm y := by
    intro y
    have h3 : τ (σ.symm y) = y := by rw [← h (σ.symm y)]; simp
    have h5 : τ.symm (τ (σ.symm y)) = σ.symm y := AlgEquiv.symm_apply_apply τ (σ.symm y)
    rw [h3] at h5
    exact h5.symm
  cases w with
  | inl v =>
    -- archimedean place: the action uses only the function `E → E`
    simp only [NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]
    ext x
    rw [NumberField.InfinitePlace.smul_apply, NumberField.InfinitePlace.smul_apply, hsymm x]
  | inr q =>
    -- nonarchimedean place: the action is induced by the ring automorphism of `𝓞 E`
    simp only [NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj]
    apply IsDedekindDomain.HeightOneSpectrum.ext
    simp only [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
    congr 1
    ext x
    exact h x

end NK.NUV2.LC.RouteB.v2
