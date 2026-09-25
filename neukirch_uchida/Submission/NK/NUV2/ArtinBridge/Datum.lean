import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.ellPart

/-!
# The canonical Artin datum (the input of the `ℓ`-adic Artin bridge)

`NK.NUV2.ArtinBridge.dualIso` — the bridge
`Dual (C_K ⧸ C_K⁰) ℓ ≃ₗ[ℤ_ℓ] Dual (Γ_K^Ω) ℓ` — was found *not* derivable from
`hFC : NK.GlobalCFTdeep.FundamentalClassElement` with the workspace library: the levelwise
reciprocity isomorphisms on disk (`NK.GlobalCFTdeep.galoisReciprocity_of_fundamentalClassElement`)
are built from `Classical.choice`-chosen fundamental classes and `H⁰`-computations, hence carry no
compatibility across levels, and Takagi's existence theorem is only a licensed input
(`NK.GlobalCFTdeep.TakagiExistence`).

This file isolates the *canonicity* input in the form in which it is consumed: a coherent system of
Artin maps on the `ℓ`-power levels of `Ω/K`, with the equality of kernels and surjectivity.  The
existence of such a system is the classical content of "the Artin map is normalised by the
Frobenius elements" (equivalently: the fundamental class is normalised by the local invariants); it
is the ingredient that makes the levelwise isomorphisms compatible with the transition maps, i.e.
that produces the limit isomorphism `C_K ⧸ C_K⁰ ≅ G_Kᵃᵇ`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT (IdeleClassGroup)

/-- **The canonical Artin datum.**  A system `art L` of continuous homomorphisms
`C_K →* Γ_{L,ℓ}` on the `ℓ`-power levels `L/K` of `Ω` which is

* **coherent**: the transition maps `ellRestrict ℓ L M h` (restriction of `Gal(M/K)ᵃᵇ` to
  `Gal(L/K)ᵃᵇ` on `ℓ`-parts) intertwine `art M` and `art L`;
* **kernel-correct**: `ker (art L) = N_{L/K}C_L` (this is the Artin reciprocity law at the level
  `L`, and it is exactly right because for `L/K` of `ℓ`-power degree the abelianisation
  `Gal(L/K)ᵃᵇ` is an `ℓ`-group, so its `ℓ`-part is all of it);
* **surjective**: `art L` is onto `Γ_{L,ℓ}`.

Such a system exists classically (the *canonical* Artin map, normalised by the Frobenius elements
of unramified primes, or equivalently by the local invariants of the fundamental class); the
systems constructed on disk by `Classical.choice` are not known to satisfy the coherence condition.
The datum is exactly what turns the levelwise isomorphisms into an isomorphism of limits
`C_K ⧸ C_K⁰ ≅ G_Kᵃᵇ`. -/
def CanonicalArtinDatum (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∃ art : ∀ (L : NK.Reconstruct.FrobLevel K Ω), IsPGroup ℓ (↥L.L ≃ₐ[K] ↥L.L) →
      IdeleClassGroup K →* NK.Reconstruct.LevelEllPart L.L ℓ,
    (∀ (L M : NK.Reconstruct.FrobLevel K Ω) (hL : IsPGroup ℓ (↥L.L ≃ₐ[K] ↥L.L))
      (hM : IsPGroup ℓ (↥M.L ≃ₐ[K] ↥M.L)) (h : L.L ≤ M.L),
      art L hL = (NK.Reconstruct.ellRestrict ℓ L M h).comp (art M hM)) ∧
    (∀ (L : NK.Reconstruct.FrobLevel K Ω) (hL : IsPGroup ℓ (↥L.L ≃ₐ[K] ↥L.L)),
      (art L hL).ker = NK.GlobalCFT.Idele.normClassSubgroup K ↥L.L) ∧
    (∀ (L : NK.Reconstruct.FrobLevel K Ω) (hL : IsPGroup ℓ (↥L.L ≃ₐ[K] ↥L.L)),
      Function.Surjective (art L hL))

end NK.NUV2.ArtinBridge
