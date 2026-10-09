import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
import Submission.Work.SSGRoute.ZDataMup.CycleAuxField
import Submission.NK.NUV2.ARL.transferSelfContained
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The auxiliary-field hypothesis of Artin's lemma for an ideal modulus

`AuxFieldHypId K L 𝔪` is the ideal-modulus form of `NK.CFTLib.ARL.AuxFieldHyp K L m` (Artin's
lemma): for every finite set `s` of primes coprime to `𝔪` there are `M > 0`, a field
`E ⊆ L(ζ_M)` with `E ∩ L = K`, and subfields `E𝔭 ≤ E` (𝔭 ∈ s) with `E𝔭·ℚ(ζ_M) = L(ζ_M)` and `𝔭`
splitting completely in `E𝔭/K`; moreover `(M)` is coprime to `𝔪` and to the primes of `s`.

It is derived from the cycle-form `Cycle.AuxFieldHyp` (proved: `Cycle.auxField_exists`).

Also collected here are the two coprimality bookkeeping lemmas of the transfer: coprimality to an
ideal modulus survives base change, and the relative norm of a coprime ideal is coprime to the
base-changed modulus.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

namespace Work.SSGRoute.ZDataMup.MupAux

open NK.CFTLib.ArtinReciprocityIdeal

/-- **The auxiliary-field hypothesis of Artin's lemma for an ideal modulus `𝔪`.** -/
def AuxFieldHypId (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) : Prop :=
  ∀ (s : Finset (NK.Chebotarev.PrimeIdeal K))
    (hs : ∀ 𝔭 ∈ s, ¬ NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime),
    ∃ (M : ℕ) (_ : NeZero M),
      (∀ 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 →
          (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal) ∧
      (∀ p ∈ S, ¬ p ∣ M) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → ∀ 𝔭 ∈ s, ¬ p ∣ Ideal.absNorm 𝔭.asIdeal) ∧
      Disjoint ((⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K)
        (IntermediateField.adjoin K
          ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
            Set (CyclotomicField M L))) ∧
      ∃ E : IntermediateField K (CyclotomicField M L),
        Disjoint E ((⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K) ∧
        (∀ 𝔭 ∈ s, ∃ E𝔭 : IntermediateField K (CyclotomicField M L),
          E𝔭 ≤ E ∧
          (E𝔭.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
            ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
              Set (CyclotomicField M L))) = ⊤ ∧
          NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥E𝔭) 𝔭 1)

/-- **Artin's lemma at an ideal modulus**: `AuxFieldHypId K L 𝔪` holds for every `𝔪`. -/
theorem auxFieldHypId {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥) :
    AuxFieldHypId K L 𝔪 := by
  classical
  intro s hs S hS
  -- the cycle of `𝔪` and its support
  have hfin : {Q : HeightOneSpectrum (𝓞 K) |
      NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 Q}.Finite := by
    refine (Ideal.finite_factors (I := 𝔪) ?_).subset ?_
    · simpa [Ideal.zero_eq_bot] using h𝔪
    · intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      exact Ideal.dvd_iff_le.mpr hp
  let c : Work.SSGRoute.ZDataMup.Cycle K :=
    ⟨hfin.toFinset, fun Q => (FractionalIdeal.count K Q (𝔪 : FractionalIdeal (𝓞 K)⁰ K)).toNat⟩
  have hc : ∀ Q : HeightOneSpectrum (𝓞 K),
      Q ∈ c.supp ↔ NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 Q :=
    fun Q => hfin.mem_toFinset
  obtain ⟨M, hMne, hMcop, hMS, hMN, hdisj, E, hEdisj, hE𝔭⟩ :=
    Work.SSGRoute.ZDataMup.Cycle.auxField_exists L c s
      (fun 𝔭 h𝔭 => fun hmem => hs 𝔭 h𝔭 ((hc 𝔭).mp hmem)) S hS
  refine ⟨M, hMne, ?_, hMS, hMN, hdisj, E, hEdisj, hE𝔭⟩
  -- `(M)` is coprime to `𝔪`: a common prime would divide `M` and `c.normProd`
  intro 𝔭 h𝔭 hmem
  obtain ⟨p, hp, hpM, hpN⟩ := NK.NUV2.ARL.SC.exists_prime_dvd_absNorm_of_mem (K := K) hmem
  have hpDvd : p ∣ c.normProd := by
    rw [Work.SSGRoute.ZDataMup.Cycle.normProd]
    exact hpN.trans (Finset.dvd_prod_of_mem
      (fun q : HeightOneSpectrum (𝓞 K) => Ideal.absNorm q.asIdeal) ((hc 𝔭).mpr h𝔭))
  exact hp.not_dvd_one (by
    rw [← hMcop.gcd_eq_one]
    exact Nat.dvd_gcd hpM hpDvd)

end Work.SSGRoute.ZDataMup.MupAux
