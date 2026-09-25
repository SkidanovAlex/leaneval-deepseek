import Mathlib
import Submission.NK.GlobalCFT.Place

/-!
# The identity of `Gal(L/K)` acts trivially on the places of `L`

For an extension `L / K` of number fields the automorphism group `Gal(L/K) = (L ≃ₐ[K] L)` acts on
the places of `L`: an archimedean place is composed with the automorphism (equivalently, pulled
back along its inverse), while a nonarchimedean place has its underlying prime pushed forward along
the induced automorphism of `𝓞 L`.

This file records the tautological first law of that action, `1 • v = v`, which is needed to turn
the bare `SMul` instance `NK.GlobalCFT.Place` puts on the places into something usable (e.g. when
computing with the action of `Gal(L/K)` on the idèle class group `C_L`).  The statement is made for
an arbitrary algebra `K → L` of number fields -- no finiteness or Galois hypothesis is required --
exactly as needed by global class field theory.
-/

open scoped NumberField
open IsDedekindDomain

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT

/-- The identity of `Gal(L/K)` acts trivially on the places of `L`.

On the archimedean places this is the `one_smul` of the Mathlib action on `InfinitePlace L`.  On
the nonarchimedean places it comes down to the fact that the automorphism of `𝓞 L` induced by the
identity fixes every prime: pushing a prime ideal along the identity ring homomorphism gives back
the same ideal. -/
theorem globalCFT_one_smul_place {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (v : NK.GlobalCFT.Place L) :
    (1 : L ≃ₐ[K] L) • v = v := by
  cases v with
  | inl w => simp
  | inr q =>
      rw [Place.smul_ofFinite, Place.ofFinite_inj]
      apply HeightOneSpectrum.ext
      rw [Place.smulHeightOneSpectrum_asIdeal]
      -- The induced automorphism of `𝓞 L` is the identity ring equivalence.
      have hσ : Place.ringOfIntegersEquiv (1 : L ≃ₐ[K] L) = RingEquiv.refl (𝓞 L) := by
        ext x
        rw [Place.ringOfIntegersEquiv_apply, RingEquiv.refl_apply, AlgEquiv.one_apply]
      rw [hσ]
      -- Pushing an ideal forward along the identity ring homomorphism does nothing.
      exact Ideal.map_id q.asIdeal

end NK.GlobalCFT.Galois
