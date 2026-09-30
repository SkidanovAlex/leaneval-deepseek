import Mathlib
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GCBasics

open CategoryTheory in
/-- The closed point of a field is the zero ideal: `Spec F` is a single point. -/
lemma closedPoint_eq_bot_of_field (F : Type _) [Field F] :
    IsLocalRing.closedPoint F = (⊥ : PrimeSpectrum F) := by
  refine PrimeSpectrum.ext ?_
  rw [PrimeSpectrum.asIdeal_bot]
  exact IsLocalRing.maximalIdeal_eq_bot

/-- Pulling back the zero prime of the fraction field of a domain along `R → Frac R` gives the
zero prime of `R`, i.e. the generic point. -/
lemma comap_algebraMap_fractionRing_bot (R : Type _) [CommRing R] [IsDomain R] :
    PrimeSpectrum.comap (algebraMap R (FractionRing R)) (⊥ : PrimeSpectrum (FractionRing R)) =
      (⊥ : PrimeSpectrum R) := by
  refine PrimeSpectrum.ext ?_
  rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot, PrimeSpectrum.asIdeal_bot,
    ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R (FractionRing R))

open CategoryTheory in
theorem genPt_apply {K : Type _} [Field K] (R : Type _) [CommRing R] [IsDomain R]
    [Algebra K R] :
    (Work.GCBasics.genPt (K := K) R).left (IsLocalRing.closedPoint (FractionRing R)) =
      genericPoint (AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  -- `genPt R` is the map on spectra induced by `R → Frac R`, so on points it is `PrimeSpectrum.comap`.
  rw [show (Work.GCBasics.genPt (K := K) R).left (IsLocalRing.closedPoint (FractionRing R))
      = PrimeSpectrum.comap (algebraMap R (FractionRing R))
          (IsLocalRing.closedPoint (FractionRing R)) from rfl]
  -- The generic point of `Spec R` for a domain is the zero ideal.
  rw [AlgebraicGeometry.genericPoint_eq_bot_of_affine]
  rw [closedPoint_eq_bot_of_field, comap_algebraMap_fractionRing_bot]

end Work.GCBasics
