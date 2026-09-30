import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Krull dimension does not increase under an integral extension

If `S` is an integral `R`-algebra, then `ringKrullDim S ≤ ringKrullDim R`.

The point is the incomparability part of the Cohen–Seidenberg theory: for an integral
extension, strictly comparable primes of `S` contract to strictly comparable primes of `R`
(`Ideal.IsIntegral.under_lt_under`). Hence `PrimeSpectrum.comap (algebraMap R S)` is a
strictly monotone map `PrimeSpectrum S → PrimeSpectrum R`, and Krull dimension is monotone
under strictly monotone maps (`Order.krullDim_le_of_strictMono`).

Note that no injectivity hypothesis is needed: for example for `ℤ → ℤ/6` the two primes of
`ℤ/6` are incomparable, so they contribute no chain, while `Spec ℤ` has dimension `1`.
-/

namespace Work.CurveBasics.BaseChange

theorem ringKrullDim_le_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim, ringKrullDim]
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  intro p q hpq
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hpq ⊢
  simp only [PrimeSpectrum.comap_asIdeal]
  exact Ideal.IsIntegral.under_lt_under hpq

end Work.CurveBasics.BaseChange
