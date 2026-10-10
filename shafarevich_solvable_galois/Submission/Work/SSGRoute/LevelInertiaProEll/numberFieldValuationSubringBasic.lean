import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Submission.Work.SSGRoute.finite_card_residueField_comap_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The valuation ring of a proper place of a number field

Let `F` be a number field and `B : ValuationSubring F` a *proper* valuation subring (a nontrivial
valuation ring of `F`).  Then `B` is the localisation of the ring of integers `𝓞 F` at a nonzero
prime `P` (`Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime`),
hence

* `B` is a discrete valuation ring (a localisation of a Dedekind domain at a maximal ideal);
* `B` is Noetherian (a DVR is a PID);
* the residue field `κ = B / 𝔪_B` is isomorphic to `𝓞 F / P`, hence a finite field;
* finite fields are perfect, and `κ ≃ 𝔽_ℓ` with `ℓ = char κ` a prime:

  `∃ ℓ f, ℓ.Prime ∧ CharP κ ℓ ∧ Nat.card κ = ℓ ^ f`.

This is the "level 0" input for the local structure theory at a finite place of the finite level
`M` in the Pro-`ℓ` inertia computation (`Work.SSGRoute.LevelInertiaProEll.levelRingBasic`).
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.LevelInertiaProEll

/-- **A proper valuation ring of a number field is a DVR with finite perfect residue field.** -/
theorem numberFieldValuationSubringBasic (F : Type*) [Field F] [NumberField F]
    (B : ValuationSubring F) (hB : B ≠ ⊤) :
    IsDiscreteValuationRing B ∧ IsNoetherianRing B ∧
      PerfectField (IsLocalRing.ResidueField B) ∧
      Finite (IsLocalRing.ResidueField B) ∧
      ∃ (ℓ f : ℕ), ℓ.Prime ∧ CharP (IsLocalRing.ResidueField B) ℓ ∧
        Nat.card (IsLocalRing.ResidueField B) = ℓ ^ f := by
  -- `B` contains `𝓞 F` and is the localisation of `𝓞 F` at a unique nonzero prime `P`.
  obtain ⟨P, hP⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime B hB
      (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top B hB)
  subst hP
  -- From now on the goal is about `V := valuationSubringAtPrime F P`.
  -- `V` is the localisation of the Dedekind domain `𝓞 F` at the maximal ideal `P`, hence a DVR.
  haveI hDVR : IsDiscreteValuationRing
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    infer_instance
  -- A DVR is a PID, hence Noetherian.
  haveI hNoeth : IsNoetherianRing
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P) := inferInstance
  -- The residue field of `V` is the residue field `𝓞 F ⧸ P` of the prime.
  obtain ⟨e⟩ := Work.SSGRoute.residueField_valuationSubringAtPrime_ringEquiv
      (R := NumberField.RingOfIntegers F) (K := F) P
  haveI hFinQ : Finite (NumberField.RingOfIntegers F ⧸ P.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum P
  haveI hFin : Finite (IsLocalRing.ResidueField
      ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P)) :=
    Finite.of_equiv (NumberField.RingOfIntegers F ⧸ P.asIdeal) e.symm.toEquiv
  -- A finite field is perfect.
  haveI hPerf : PerfectField (IsLocalRing.ResidueField
      ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P)) := inferInstance
  -- A finite field is `𝔽_ℓ` with `ℓ = char` a prime.
  haveI : Fintype (IsLocalRing.ResidueField
      ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P)) := Fintype.ofFinite _
  obtain ⟨ℓ, hℓchar, f, hℓprime, hcard⟩ := FiniteField.card' (IsLocalRing.ResidueField
      ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P))
  exact ⟨hDVR, hNoeth, hPerf, hFin, ℓ, (f : ℕ), hℓprime, hℓchar, by
    rw [Nat.card_eq_fintype_card, hcard]⟩

end Work.SSGRoute.LevelInertiaProEll
