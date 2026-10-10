import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.swCount_eq_zero
import Submission.Work.SSGRoute.H9.swHistK
import Submission.Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The escape normalisation of a `HistK` history, modulo `p`

`Work.SSGRoute.H9.HistK`'s normalisation clause records only the *existence* of a uniformiser `u` at
the escape prime `Q_m` with `χ_{b_m · u} = 0` on the decomposition group — i.e.
`v_{Q_m}(b_m) ≡ −1 (mod p)` — and not the exact integer identity `count = −1` that
`Work.SSGRoute.H9.swChainValueH9` consumes.  This file bridges the gap: from the clause one gets

  `((count_𝔮 (b_m) : ℤ) : ZMod p) = -1`

for `𝔮` the prime of `𝓞 ↥K` below `Q_m`, by applying the two halves of the Kummer dictionary:

* `χ_{b_m · u} = 0` on the inertia at `Q_m` makes the Kummer level `K((b_m u)^{1/p})` unramified at
  `𝔮` (`Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia`);
* an unramified Kummer level forces `p ∣ v_𝔮(b_m u)`
  (`Work.SSGRoute.H9.swCount_eq_zero_of_isUnramifiedIn_hLevel`).

Together with `count(u) = 1` this is the normalisation modulo `p`.
-/

namespace Work.SSGRoute.NodeS35

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- **The escape normalisation of a `HistK` history, in `ZMod p`.**  At the prime `𝔮` of `𝓞 ↥K`
below the `m`-th escape prime, the `𝔮`-count of the `m`-th element of the history is `-1` modulo
`p`. -/
theorem histCount_modp {K N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [NumberField ↥K] [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (hf : Work.SSGRoute.H9.HistK (p := p) K N ζ hζ hζK S y f) (m : ℕ)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔮 : ((f m).1).comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮) :
    ((FractionalIdeal.count ↥K 𝔮 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ((f m).2 : ↥K)) : ℤ) : ZMod p) = -1 := by
  classical
  -- the normalisation clause of the history
  obtain ⟨hfin, -, -, -, -, -, hnorm⟩ := hf
  obtain ⟨u, ⟨𝔮', h𝔮'def, h𝔮'count⟩, hχ⟩ := hnorm m
  -- the prime below the escape prime is the one prescribed by the caller
  have h𝔮eq : 𝔮' = 𝔮 := by
    refine (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥K) (K := ↥K)) ?_
    rw [← h𝔮'def, h𝔮]
  -- the Kummer level of `b_m · u`
  haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) ((f m).2 * u)) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) ((f m).2 * u)
  haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) ((f m).2 * u)) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) ((f m).2 * u)
  haveI hnf : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) ((f m).2 * u)) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) ((f m).2 * u)
  -- `χ_{b_m · u}` kills the inertia at the escape prime
  have hkill : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k ((f m).1) σ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ ((f m).2 * u) σ = 0 :=
    fun σ hσ hσI => hχ σ hσ hσI.1
  -- hence the Kummer level of `b_m · u` is unramified at `𝔮`
  have hodd : Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ((f m).1) (hfin m) = 𝔮 := by
    refine (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥K) (K := ↥K)) ?_
    rw [← Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := (f m).1) (hfin m),
      h𝔮'def, h𝔮eq]
  have hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) ((f m).2 * u))) 𝔮 := by
    rw [← hodd]
    exact Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := p) ζ hζ hζK
      ((f m).2 * u) ((f m).1) (hfin m) hkill
  -- and the unramified Kummer level has `count ≡ 0 (mod p)`
  have h0 := Work.SSGRoute.H9.swCount_eq_zero_of_isUnramifiedIn_hLevel (K := K) (p := p) ζ hζ hζK
    ((f m).2 * u) 𝔮 hunr
  -- multiplicativity of the count
  have hmulq : FractionalIdeal.count ↥K 𝔮' (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (((f m).2 * u : (↥K)ˣ) : ↥K))
      = FractionalIdeal.count ↥K 𝔮' (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ((f m).2 : ↥K)) + 1 := by
    have hb : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((f m).2 : ↥K) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)
    have hu : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (u : ↥K) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)
    rw [show (((f m).2 * u : (↥K)ˣ) : ↥K) = ((f m).2 : ↥K) * (u : ↥K) from Units.val_mul _ _,
      ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul ↥K 𝔮' hb hu, h𝔮'count]
  have hmul := hmulq
  rw [h𝔮eq] at hmul
  -- conclude
  rw [hmul] at h0
  have hcast : ((FractionalIdeal.count ↥K 𝔮 (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ((f m).2 : ↥K)) : ℤ) : ZMod p) + 1 = 0 := by
    simpa using h0
  simpa using (add_eq_zero_iff_eq_neg.mp hcast)

end Work.SSGRoute.NodeS35
