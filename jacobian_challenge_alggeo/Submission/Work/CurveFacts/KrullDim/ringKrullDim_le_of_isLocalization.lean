import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveFacts.KrullDim

universe u

/-- **Localization does not increase Krull dimension.**  If `S` is the localization of `R` at a
submonoid `M ⊆ R`, then `ringKrullDim S ≤ ringKrullDim R`.

Proof route: the primes of `S` are the primes of `R` avoiding `M`; Mathlib's
`IsLocalization.primeSpectrumOrderIso` gives an order isomorphism
`PrimeSpectrum S ≃o {p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal}`, whose composite
with the subtype inclusion is strictly monotone, so `Order.krullDim_le_of_strictMono` gives the
claim after rewriting `ringKrullDim` as `Order.krullDim` of the prime spectrum. -/
theorem ringKrullDim_le_of_isLocalization {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    ringKrullDim S ≤ ringKrullDim R := by
  -- The composite `PrimeSpectrum S → {p // Disjoint M p.asIdeal} → PrimeSpectrum R` is strictly
  -- monotone, being the composite of an order isomorphism and the subtype inclusion.
  have h : StrictMono (fun p : PrimeSpectrum S =>
      (IsLocalization.primeSpectrumOrderIso M S p).1 : PrimeSpectrum S → PrimeSpectrum R) :=
    (Subtype.strictMono_coe _).comp (IsLocalization.primeSpectrumOrderIso M S).strictMono
  exact Order.krullDim_le_of_strictMono _ h

end Work.CurveFacts.KrullDim
