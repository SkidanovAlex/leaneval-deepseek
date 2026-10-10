import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Height does not decrease along flat ring maps

If `A → B` is a flat ring map and `P` is a prime of `B` lying over a prime `p` of `A`,
then `height p ≤ height P`. This is an immediate consequence of the going-down property
of flat algebras (`Algebra.HasGoingDown.of_flat`): every strictly decreasing chain of
primes below `p` lifts to a strictly decreasing chain of the same length below `P`, so
the supremum of the lengths cannot decrease.

The `IsNoetherianRing A` hypothesis is not needed for the inequality (it is harmless).
-/

namespace Work.CY3Stab.Prod

theorem height_le_height_of_flat {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime]
    (hP : P.LiesOver p) : p.height ≤ P.height := by
  -- Rewrite the heights of prime ideals as heights in the prime spectra, ordered by inclusion.
  rw [show p.height = Order.height (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum A) from
        PrimeSpectrum.height_eq_orderHeight (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum A),
      show P.height = Order.height (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum B) from
        PrimeSpectrum.height_eq_orderHeight (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum B)]
  -- It suffices to lift every chain below `p` to a chain of equal length below `P`.
  refine Order.height_le_iff'.mpr fun l hl => ?_
  have hlo : P.LiesOver l.last.asIdeal := by
    rw [show l.last.asIdeal = p from congrArg PrimeSpectrum.asIdeal hl]
    exact hP
  -- Going down for the flat algebra `A → B` lifts the chain.
  obtain ⟨L, hlen, hlast, -⟩ :=
    Ideal.exists_ltSeries_of_hasGoingDown l P (lo := hlo)
  rw [← hlen]
  have h1 : L.length ≤ Order.height L.last := Order.length_le_height_last
  rw [hlast] at h1
  exact h1.trans (le_of_eq (congrArg Order.height (PrimeSpectrum.ext rfl)))

end Work.CY3Stab.Prod
