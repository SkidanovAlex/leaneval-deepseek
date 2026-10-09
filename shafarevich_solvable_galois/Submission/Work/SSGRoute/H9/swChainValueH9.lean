import Mathlib
import Submission.Work.SSGRoute.H9.swChainConjDefs
import Submission.Work.SSGRoute.H9.swTwoPlacePairing
import Submission.Work.SSGRoute.H9.swDictionaryKills
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The §4(b) chain value identity of Schmidt--Wingberg, via conjugates

The assembly of the derivation of `H9/NOTE_chain_route_conjugates.md`: the value identity
`χ_{b_i}(ψ_N^σ) + χ_{b_N}(ψ_N^σ) = 0` at a Frobenius of the local group of a sibling of the last
escape prime, which is the `hchain` input of `Work.SSGRoute.H9.ZSix_of_histK`.

The derivation pairs each escape class with the *conjugate* of an escape class at the sibling of the
other escape prime:

* `(S1)`, `(S3)`: the two-place product formula `H9.swTwoPlacePairing_zero` at the place pairs
  `(Q_i, σQ_i)` and `(Q_i, σQ_N)`;
* `(d1)`, `(d5)`: the local dictionary `H9.swPairingValueFrob_of_kills` at the siblings;
* `(d2)`, `(d6)`: the transposed dictionary `H9.swPairingValueFrob_of_kills_swap` at the escape
  prime `Q_i` (where `χ_{b_i}` is ramified, so one must transpose);
* `(γ)`: the prescription transported to the conjugates, `H9.swPresc_conjUnit`;
* `(δ)`: the prescription at the sibling, `H9.swPresc_sibling`;
* the shoe-box matching `χ_{b_N}(ψ_N^σ) = χ_{b_i}(ψ_i^σ)`.

The inputs which are *not* bookkeeping are the confinements, the escape normalisations
(`count ≡ −1`, whose transport to the siblings is `H9.swCount_conjUnit`), the prescription, and the
four Frobenius *pinnings* of the Kummer levels.
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup
open Work.SSGRoute.ZDataMup.OddForm

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- **The §4(b) chain value identity.** -/
theorem swChainValueH9 {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω]
    (hp : p ≠ 2) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (bi bN : (↥K)ˣ) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (Qi QN : ValuationSubring Ω)
    (hQifin : SSGRoute.IsFinPlace k Qi) (hQifin' : SSGRoute.IsFinPlace k (galLift K σ • Qi))
    (hQisplit : SSGRoute.IsSplitIn k K Qi)
    (hQNfin' : SSGRoute.IsFinPlace k (galLift K σ • QN))
    (hZiN1 : ¬ Work.SSGRoute.gesKConj K Qi (galLift K σ • Qi))
    (hZiN1' : ¬ Work.SSGRoute.gesKConj K (galLift K σ • Qi) Qi)
    (hZiN3 : ¬ Work.SSGRoute.gesKConj K Qi (galLift K σ • QN))
    (hZiN3' : ¬ Work.SSGRoute.gesKConj K (galLift K σ • QN) Qi)
    -- the confinements (at the two escape primes and the two siblings)
    (hconf_i : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Qi B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi u = 0)
    (hconf_σi : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K (galLift K σ • Qi) B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (conjUnit (galLift K σ) bi) u = 0)
    (hconf_σN : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K (galLift K σ • QN) B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (conjUnit (galLift K σ) bN) u = 0)
    -- the escape normalisations
    (hcount_i : FractionalIdeal.count ↥K (oddPrime (K := K) Qi hQifin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bi : ↥K)) = -1)
    (hcount_σi : FractionalIdeal.count ↥K (oddPrime (K := K) (galLift K σ • Qi) hQifin')
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((conjUnit (galLift K σ) bi : (↥K)ˣ) : ↥K)) = -1)
    (hcount_σN : FractionalIdeal.count ↥K (oddPrime (K := K) (galLift K σ • QN) hQNfin')
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((conjUnit (galLift K σ) bN : (↥K)ˣ) : ↥K)) = -1)
    -- the prescription at the siblings of the first escape prime
    (hpresc : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k Qi Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • Qi = Q) →
      ∀ y ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi y
          + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN y = 0)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) bi)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) bi)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) bi)]
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (conjUnit (galLift K σ) bi))]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (conjUnit (galLift K σ) bi))]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) (conjUnit (galLift K σ) bi))]
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (conjUnit (galLift K σ) bN))]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (conjUnit (galLift K σ) bN))]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) (conjUnit (galLift K σ) bN))]
    -- the Frobenius elements and their pinnings
    (ψi ψiσ ψN : Ω ≃ₐ[k] Ω)
    (hψi : ψi ∈ SSGRoute.decomp k Qi ⊓ K.fixingSubgroup)
    (hψiσ : ψiσ ∈ SSGRoute.decomp k (galLift K σ • Qi) ⊓ K.fixingSubgroup)
    (hψN : ψN ∈ SSGRoute.decomp k (galLift K σ • QN) ⊓ K.fixingSubgroup)
    (hpin_iσ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := p) bi)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψiσ, (Subgroup.mem_inf.mp hψiσ).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) bi))
        (oddPrime (K := K) (galLift K σ • Qi) hQifin'))
    (hpin_N : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := p) bi)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψN, (Subgroup.mem_inf.mp hψN).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) bi))
        (oddPrime (K := K) (galLift K σ • QN) hQNfin'))
    (hpin_iσi : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := p) (conjUnit (galLift K σ) bi))
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψi, (Subgroup.mem_inf.mp hψi).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (conjUnit (galLift K σ) bi)))
        (oddPrime (K := K) Qi hQifin))
    (hpin_iσN : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := p) (conjUnit (galLift K σ) bN))
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψi, (Subgroup.mem_inf.mp hψi).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (conjUnit (galLift K σ) bN)))
        (oddPrime (K := K) Qi hQifin))
    -- the shoe-box matching
    (hmatch : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN ψN
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψiσ) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψN
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN ψN = 0 := by
  classical
  set ζ' : ↥K := ⟨ζ, hζK⟩ with hζ'def
  have hζ' : IsPrimitiveRoot ζ' p :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- ## The product formulae
  have hS1 := swTwoPlacePairing_zero (K := K) (p := p) (k := k) (Ω := Ω) hp ζ hζ hζK bi
    (conjUnit (galLift K σ) bi) Qi (galLift K σ • Qi) hQifin hQifin' hZiN1 hconf_i hconf_σi
  have hS3 := swTwoPlacePairing_zero (K := K) (p := p) (k := k) (Ω := Ω) hp ζ hζ hζK bi
    (conjUnit (galLift K σ) bN) Qi (galLift K σ • QN) hQifin hQNfin' hZiN3 hconf_i hconf_σN
  -- ## The four dictionary readings
  have hd1 := swPairingValueFrob_of_kills (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hζK bi
    (conjUnit (galLift K σ) bi) (galLift K σ • Qi) hQifin'
    (fun u _ hI => hconf_i _ hQifin' hZiN1 u hI) ψiσ (Subgroup.mem_inf.mp hψiσ).2 hpin_iσ
  have hd5 := swPairingValueFrob_of_kills (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hζK bi
    (conjUnit (galLift K σ) bN) (galLift K σ • QN) hQNfin'
    (fun u _ hI => hconf_i _ hQNfin' hZiN3 u hI) ψN (Subgroup.mem_inf.mp hψN).2 hpin_N
  have hd2 := swPairingValueFrob_of_kills_swap (K := K) (p := p) (k := k) (Ω := Ω) hp ζ hζ hζK
    bi (conjUnit (galLift K σ) bi) Qi hQifin
    (fun u _ hI => hconf_σi _ hQifin hZiN1' u hI) ψi (Subgroup.mem_inf.mp hψi).2 hpin_iσi
  have hd6 := swPairingValueFrob_of_kills_swap (K := K) (p := p) (k := k) (Ω := Ω) hp ζ hζ hζK
    bi (conjUnit (galLift K σ) bN) Qi hQifin
    (fun u _ hI => hconf_σN _ hQifin hZiN3' u hI) ψi (Subgroup.mem_inf.mp hψi).2 hpin_iσN
  -- ## (I), (III), (IV), (δ)
  have hI : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (conjUnit (galLift K σ) bi) ψi
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψiσ := by
    rw [hd1, hd2] at hS1
    rw [hcount_σi, hcount_i] at hS1
    simp only [neg_one_smul, neg_neg] at hS1
    exact add_neg_eq_zero.mp hS1
  have hIII : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (conjUnit (galLift K σ) bN) ψi
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψN := by
    rw [hd5, hd6] at hS3
    rw [hcount_σN, hcount_i] at hS3
    simp only [neg_one_smul, neg_neg] at hS3
    exact add_neg_eq_zero.mp hS3
  have hIV := swPresc_conjUnit (K := K) (p := p) ζ hζ hζK bi bN σ hσ Qi hQisplit hpresc
  -- ## assembly
  have key : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψN
      = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψiσ := by
    have h := hIV ψi hψi
    rw [hIII] at h
    have h2 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψN
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (conjUnit (galLift K σ) bi) ψi = 0 := by
      rw [add_comm]; exact h
    rw [add_eq_zero_iff_eq_neg.mp h2, hI]
  rw [hmatch, key]
  exact neg_add_cancel _

end Work.SSGRoute.H9
