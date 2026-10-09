import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.H9.swHistK
import Submission.Work.SSGRoute.H9.swHistChi_confinement_proved
import Submission.Work.SSGRoute.H9.swHistChi_presc_proved
import Submission.Work.SSGRoute.H9.swCount_conjUnit
import Submission.Work.SSGRoute.ZDataMup.swTriggerPlace
import Submission.Work.SSGRoute.NodeS35.swPinFamily
import Submission.Work.SSGRoute.NodeS35.swHchainBasic
import Submission.Work.SSGRoute.NodeS35.swChainValueH9_modp
import Submission.Work.SSGRoute.NodeS35.histCount
import Submission.Work.SSGRoute.NodeS35.kills_inertia_conjUnit
import Submission.Work.SSGRoute.NodeS35.isUnramifiedIn_sup_hLevel
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.SupStructure
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.galois_sup_structure
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.HonestPairing

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# The value identity of the §4(b) chain at the last escape prime

This module proves `Work.SSGRoute.ZDataMup.swHvalAtSiblingSelf`: the two-place product formula of
Schmidt--Wingberg §4(b) instantiated at the pipe of escape primes selected by the shoe box.  It is
the single arithmetic input of the assembly of `Work.SSGRoute.ZDataMup.sw_odd_kummer_core`, which
consumes it (and *promotes* it to the whole local group with `NodeS34.swKLevel_sum_vanish`).

The proof is the chain of the paper: the two-place reciprocities `H9.swTwoPlacePairing_zero` at the
pairs `(Q_i, σQ_i)` and `(Q_i, σQ_N)` are read through the local dictionaries
`H9.swPairingValueFrob_of_kills` and `H9.swPairingValueFrob_of_kills_swap`
(and `H9.swPresc_conjUnit`), with the escape normalisations supplied by `NodeS35.histCount_modp`
and `H9.swCount_conjUnit`, the four Frobenius pinnings by `NodeS35.exists_pinned_at` /
`NodeS35.exists_pinned` / `NodeS35.pin_of_le`, and the shoe-box matching by
`NodeS35.pinValue_eq`.  Everything is packaged by `NodeS35.swChainValueH9_modp`; this module's only
content is the discharge of its hypothesis list from a `HistK` history. -/

/-- **The value identity of the §4(b) chain at the last escape prime.** -/
theorem swHvalAtSiblingSelf {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [NumberField ↥K] [IsSepClosure ↥K Ω]
    (hKN : K ≤ N) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (hf : Work.SSGRoute.H9.HistK (p := p) K N ζ hζ hζK S y f)
    (i j : ℕ) (hij : i < j)
    (hmatch : ∀ σ : K ≃ₐ[k] K,
      Work.SSGRoute.NodeS35.pinValue (K := K) (p := p) ζ hζ hζK f (hf.1) j σ
        = Work.SSGRoute.NodeS35.pinValue (K := K) (p := p) ζ hζ hζK f (hf.1) i σ)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (hfinσ : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1))
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f i).2
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) (f j).2)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f i).2
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) (f j).2)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) (f i).2
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) (f j).2)] :
    ∃ (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1)
        ⊓ K.fixingSubgroup),
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        ↥(hLevel (Ω := Ω) (K := K) (p := p) (f i).2 ⊔ hLevel (Ω := Ω) (K := K) (p := p) (f j).2)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩) =
        NK.Chebotarev.frobAtPrime (K := ↥K)
          (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (f i).2
            ⊔ hLevel (Ω := Ω) (K := K) (p := p) (f j).2))
          (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
            (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1) hfinσ) ∧
      Work.SSGRoute.H9.histChi K ζ hζK hζ f i ψ
        + Work.SSGRoute.H9.histChi K ζ hζK hζ f j ψ = 0 := by
  classical
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- ## 0. abbreviations
  set bi : (↥K)ˣ := (f i).2 with hbi
  set bN : (↥K)ˣ := (f j).2 with hbN
  set Qi : ValuationSubring Ω := (f i).1 with hQi'
  set QN : ValuationSubring Ω := (f j).1 with hQN'
  set ρ : Ω ≃ₐ[k] Ω := Work.SSGRoute.ZDataMup.galLift K σ with hρ
  -- ## 1. bookkeeping of the two escape primes
  have hQi_fin : SSGRoute.IsFinPlace k Qi := hf.1 i
  have hQN_fin : SSGRoute.IsFinPlace k QN := hf.1 j
  have hQi_splitK : SSGRoute.IsSplitIn k K Qi :=
    fun τ hτ => IntermediateField.fixingSubgroup_le hKN (hf.2.1 i hτ)
  have hkdisj : ¬ SSGRoute.IsConjPlace k Qi QN :=
    Work.SSGRoute.H9.histK_escape_kdisj (K := K) (N := N) ζ hζ hζK S y f hf hij
  have hA_i : SSGRoute.IsFinPlace k (ρ • Qi) :=
    (SSGRoute.isFinPlace_smul_iff (k := k) Qi ρ).mpr hQi_fin
  have hA_j : SSGRoute.IsFinPlace k (ρ • QN) :=
    (SSGRoute.isFinPlace_smul_iff (k := k) QN ρ).mpr hQN_fin
  -- ## 2. the separations
  have hZiN1 : ¬ Work.SSGRoute.gesKConj K Qi (ρ • Qi) :=
    Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hσ hQi_splitK
  have hZiN1' : ¬ Work.SSGRoute.gesKConj K (ρ • Qi) Qi :=
    fun h => hZiN1 (Work.SSGRoute.ZDataMup.swTrigGesKConj_symm K h)
  have hZiN3 : ¬ Work.SSGRoute.gesKConj K Qi (ρ • QN) := by
    intro h
    exact hkdisj (SSGRoute.isConjPlace_trans
      (Work.SSGRoute.ZDataMup.swTrigGesKConj_imp_conjPlace K h)
      ⟨ρ⁻¹, by rw [inv_smul_smul]⟩)
  have hZiN3' : ¬ Work.SSGRoute.gesKConj K (ρ • QN) Qi :=
    fun h => hZiN3 (Work.SSGRoute.ZDataMup.swTrigGesKConj_symm K h)
  -- ## 3. the confinements (in the form without the membership, using the off-support vanishing)
  have hconfin_i : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Qi B) →
      ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi u = 0 :=
    Work.SSGRoute.H9.swHistChi_confinement_proved (p := p) hp K N ζ hζ hζK S y hyT f hf i
  have hconfin_j : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K QN B) →
      ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN u = 0 :=
    Work.SSGRoute.H9.swHistChi_confinement_proved (p := p) hp K N ζ hζ hζK S y hyT f hf j
  have hconf_i : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Qi B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi u = 0 := by
    intro B hB hnot u huI
    by_cases huK : u ∈ K.fixingSubgroup
    · exact hconfin_i B hB hnot u huK huI
    · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem huK
  have hconf_σi : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K (ρ • Qi) B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit ρ bi) u = 0 := by
    intro B hB hnot u huI
    by_cases huK : u ∈ K.fixingSubgroup
    · exact Work.SSGRoute.NodeS35.kills_inertia_conjUnit (K := K) (p := p) ζ hζ hζK bi σ Qi
        hconfin_i B hB hnot u huK huI
    · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem huK
  have hconf_σN : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K (ρ • QN) B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit ρ bN) u = 0 := by
    intro B hB hnot u huI
    by_cases huK : u ∈ K.fixingSubgroup
    · exact Work.SSGRoute.NodeS35.kills_inertia_conjUnit (K := K) (p := p) ζ hζ hζK bN σ QN
        hconfin_j B hB hnot u huK huI
    · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem huK
  -- ## 4. the escape normalisations
  have hcount_i : ((FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qi hQi_fin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bi : ↥K)) : ℤ) : ZMod p) = -1 :=
    Work.SSGRoute.NodeS35.histCount_modp (K := K) (N := N) ζ hζ hζK S y f hf i
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qi hQi_fin)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := Qi) hQi_fin)
  have hcount_σi : ((FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (ρ • Qi) hA_i)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((Work.SSGRoute.H9.conjUnit ρ bi : (↥K)ˣ) : ↥K)) : ℤ) : ZMod p) = -1 := by
    rw [Work.SSGRoute.H9.swCount_conjUnit (K := K) bi σ Qi hQi_fin hA_i]
    exact hcount_i
  have hcount_σN : ((FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (ρ • QN) hA_j)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((Work.SSGRoute.H9.conjUnit ρ bN : (↥K)ˣ) : ↥K)) : ℤ) : ZMod p) = -1 := by
    rw [Work.SSGRoute.H9.swCount_conjUnit (K := K) bN σ QN hQN_fin hA_j]
    exact Work.SSGRoute.NodeS35.histCount_modp (K := K) (N := N) ζ hζ hζK S y f hf j
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) QN hQN_fin)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := QN) hQN_fin)
  -- ## 5. the prescription
  have hpresc : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k Qi Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • Qi = Q) →
      ∀ y ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi y
          + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN y = 0 :=
    Work.SSGRoute.H9.swHistChi_presc_proved (p := p) hp K N ζ hζ hζK S y f hf i j hij
  -- ## 6. the instances of the levels
  haveI hfd_bi : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) bi) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bi
  haveI hgal_bi : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) bi) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bi
  haveI hnf_bi : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) bi) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bi
  haveI hfd_bN : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) bN) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bN
  haveI hgal_bN : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) bN) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bN
  haveI hnf_bN : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) bN) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bN
  haveI hfd_ci : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bi)) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
      (Work.SSGRoute.H9.conjUnit ρ bi)
  haveI hgal_ci : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bi)) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
      (Work.SSGRoute.H9.conjUnit ρ bi)
  haveI hnf_ci : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bi)) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
      (Work.SSGRoute.H9.conjUnit ρ bi)
  haveI hfd_cN : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bN)) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
      (Work.SSGRoute.H9.conjUnit ρ bN)
  haveI hgal_cN : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bN)) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
      (Work.SSGRoute.H9.conjUnit ρ bN)
  haveI hnf_cN : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bN)) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
      (Work.SSGRoute.H9.conjUnit ρ bN)
  -- the compositum `M` of the two Kummer levels of the live stages
  haveI hfdM : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) bi
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN) :=
    hLevel_sup_finiteDimensional (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bi bN
  have hsupstruct := galois_sup_general (F := ↥K) (Ω := Ω) (p := p)
      (hLevel (Ω := Ω) (K := K) (p := p) bi) (hLevel (Ω := Ω) (K := K) (p := p) bN)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bi)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bN)
      (hLevel_aut_pow_eq_one (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bi)
      (hLevel_aut_pow_eq_one (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bN)
  have hgalM : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) bi
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN) := hsupstruct.1
  have hcommM : ∀ a b : ↥(hLevel (Ω := Ω) (K := K) (p := p) bi
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) bi
        ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN), a * b = b * a := hsupstruct.2.1
  haveI hnormM : Normal ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) bi
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN) := hgalM.to_normal
  haveI hnfM : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) bi
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN) := by
    haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) bi
        ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN) := hfdM
    exact Commons.NumberTheory.NumberField.numberField_of_intermediateField
      (hLevel (Ω := Ω) (K := K) (p := p) bi ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN)
  -- the compositum `Mi` of the two conjugate Kummer levels at `Qi`
  haveI hfdMi : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bi) ⊔ hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bN)) :=
    hLevel_sup_finiteDimensional (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
      (Work.SSGRoute.H9.conjUnit ρ bi) (Work.SSGRoute.H9.conjUnit ρ bN)
  have hsupstructi := galois_sup_general (F := ↥K) (Ω := Ω) (p := p)
      (hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi))
      (hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN))
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.H9.conjUnit ρ bi))
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.H9.conjUnit ρ bN))
      (hLevel_aut_pow_eq_one (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.H9.conjUnit ρ bi))
      (hLevel_aut_pow_eq_one (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.H9.conjUnit ρ bN))
  have hgalMi : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bi) ⊔ hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bN)) := hsupstructi.1
  have hcommMi : ∀ a b : ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bi) ⊔ hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bN)) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi)
        ⊔ hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN)),
      a * b = b * a := hsupstructi.2.1
  haveI hnormMi : Normal ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bi) ⊔ hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bN)) := hgalMi.to_normal
  haveI hnfMi : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bi) ⊔ hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit ρ bN)) := by
    haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p)
        (Work.SSGRoute.H9.conjUnit ρ bi) ⊔ hLevel (Ω := Ω) (K := K) (p := p)
        (Work.SSGRoute.H9.conjUnit ρ bN)) := hfdMi
    exact Commons.NumberTheory.NumberField.numberField_of_intermediateField
      (hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi)
        ⊔ hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN))
  -- ## 7. unramifiedness of the levels at the relevant places
  have hunrM : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) bi ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (ρ • QN) hA_j) :=
    Work.SSGRoute.NodeS35.isUnramifiedIn_sup_hLevel (K := K) (p := p) ζ hζ hζK bi bN (ρ • QN)
      hA_j
      (fun u huK huI => hconfin_i (ρ • QN) hA_j hZiN3 u huK huI)
      (fun u huK huI => hconfin_j (ρ • QN) hA_j
        (Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hσ (by
          rw [hQN']; exact fun τ hτ => IntermediateField.fixingSubgroup_le hKN (hf.2.1 j hτ)))
        u huK huI)
  have hunr_bi : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) bi))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (ρ • QN) hA_j) :=
    Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := p) ζ hζ hζK bi
      (ρ • QN) hA_j (fun u huK huI => hconfin_i (ρ • QN) hA_j hZiN3 u huK huI)
  have hunr_bN : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) bN))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (ρ • QN) hA_j) :=
    Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := p) ζ hζ hζK bN
      (ρ • QN) hA_j (fun u huK huI => hconfin_j (ρ • QN) hA_j
        (Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hσ (by
          rw [hQN']; exact fun τ hτ => IntermediateField.fixingSubgroup_le hKN (hf.2.1 j hτ)))
        u huK huI)
  have hunrMi : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi)
        ⊔ hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN)))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qi hQi_fin) :=
    Work.SSGRoute.NodeS35.isUnramifiedIn_sup_hLevel (K := K) (p := p) ζ hζ hζK
      (Work.SSGRoute.H9.conjUnit ρ bi) (Work.SSGRoute.H9.conjUnit ρ bN) Qi hQi_fin
      (fun u huK huI => hconf_σi Qi hQi_fin hZiN1' u huI)
      (fun u huK huI => hconf_σN Qi hQi_fin hZiN3' u huI)
  have hunr_ci : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi)))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qi hQi_fin) :=
    Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := p) ζ hζ hζK
      (Work.SSGRoute.H9.conjUnit ρ bi) Qi hQi_fin
      (fun u huK huI => hconf_σi Qi hQi_fin hZiN1' u huI)
  have hunr_cN : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN)))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qi hQi_fin) :=
    Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := p) ζ hζ hζK
      (Work.SSGRoute.H9.conjUnit ρ bN) Qi hQi_fin
      (fun u huK huI => hconf_σN Qi hQi_fin hZiN3' u huI)
  -- ## 8. the pinned Frobenius elements
  -- `ψN`: pinned at `M` at the sibling of the last escape prime
  obtain ⟨⟨ψN, hψN_mem⟩, hpinM⟩ := Work.SSGRoute.NodeS35.exists_pinned_at
    (K := K) (k := k) (Ω := Ω)
    (hLevel (Ω := Ω) (K := K) (p := p) bi ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN)
    hcommM (ρ • QN) hA_j hunrM
  have hψN : ψN ∈ SSGRoute.decomp k (ρ • QN) ⊓ K.fixingSubgroup := hψN_mem
  have hpin_N : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
      ↥(hLevel (Ω := Ω) (K := K) (p := p) bi)
      ((IntermediateField.fixingSubgroupEquiv K) ⟨ψN, (Subgroup.mem_inf.mp hψN).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) bi))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (ρ • QN) hA_j) :=
    Work.SSGRoute.NodeS35.pin_of_le (K := K)
      (L := hLevel (Ω := Ω) (K := K) (p := p) bi)
      (M := hLevel (Ω := Ω) (K := K) (p := p) bi ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN)
      le_sup_left
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bi)
      hcommM _ hunrM hunr_bi _ hpinM
  have hpin_Nj : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
      ↥(hLevel (Ω := Ω) (K := K) (p := p) bN)
      ((IntermediateField.fixingSubgroupEquiv K) ⟨ψN, (Subgroup.mem_inf.mp hψN).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) bN))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (ρ • QN) hA_j) :=
    Work.SSGRoute.NodeS35.pin_of_le (K := K)
      (L := hLevel (Ω := Ω) (K := K) (p := p) bN)
      (M := hLevel (Ω := Ω) (K := K) (p := p) bi ⊔ hLevel (Ω := Ω) (K := K) (p := p) bN)
      le_sup_right
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' bN)
      hcommM _ hunrM hunr_bN _ hpinM
  -- `ψiσ`: pinned at `hLevel bi` at the sibling of the first escape prime
  have hkill_iσ : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k (ρ • Qi) u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi u = 0 :=
    fun u huK huI => hconfin_i (ρ • Qi) hA_i hZiN1 u huK huI
  obtain ⟨⟨ψiσ, hψiσ_mem⟩, hpin_iσ⟩ :=
    Work.SSGRoute.NodeS35.exists_pinned (K := K) (p := p) ζ hζ hζK f i (ρ • Qi) hA_i hkill_iσ
  have hψiσ : ψiσ ∈ SSGRoute.decomp k (ρ • Qi) ⊓ K.fixingSubgroup := hψiσ_mem
  -- `ψi`: pinned at the two conjugate Kummer levels at the first escape prime
  obtain ⟨⟨ψi, hψi_mem⟩, hpinMi⟩ := Work.SSGRoute.NodeS35.exists_pinned_at
    (K := K) (k := k) (Ω := Ω)
    (hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi)
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN))
    hcommMi Qi hQi_fin hunrMi
  have hψi : ψi ∈ SSGRoute.decomp k Qi ⊓ K.fixingSubgroup := hψi_mem
  have hpin_iσi : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
      ↥(hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi))
      ((IntermediateField.fixingSubgroupEquiv K) ⟨ψi, (Subgroup.mem_inf.mp hψi).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi)))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qi hQi_fin) :=
    Work.SSGRoute.NodeS35.pin_of_le (K := K)
      (L := hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi))
      (M := hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi)
        ⊔ hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN))
      le_sup_left
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.H9.conjUnit ρ bi))
      hcommMi _ hunrMi hunr_ci _ hpinMi
  have hpin_iσN : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
      ↥(hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN))
      ((IntermediateField.fixingSubgroupEquiv K) ⟨ψi, (Subgroup.mem_inf.mp hψi).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN)))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qi hQi_fin) :=
    Work.SSGRoute.NodeS35.pin_of_le (K := K)
      (L := hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN))
      (M := hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bi)
        ⊔ hLevel (Ω := Ω) (K := K) (p := p) (Work.SSGRoute.H9.conjUnit ρ bN))
      le_sup_right
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.H9.conjUnit ρ bN))
      hcommMi _ hunrMi hunr_cN _ hpinMi
  -- ## 9. the shoe-box matching
  have hmatch' : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN ψN
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψiσ := by
    rw [Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := p) ζ hζ hζK f hf.1 j σ hσ ψN hψN hpin_Nj,
      Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := p) ζ hζ hζK f hf.1 i σ hσ ψiσ hψiσ hpin_iσ,
      hmatch σ]
  -- ## 10. the chain, in the form of `swChainValueH9_modp`
  have hsum := Work.SSGRoute.NodeS35.swChainValueH9_modp (K := K) (p := p) hp ζ hζ hζK bi bN σ hσ
    Qi QN hQi_fin hA_i hQi_splitK hA_j hZiN1 hZiN1' hZiN3 hZiN3' hconf_i hconf_σi hconf_σN
    hcount_i hcount_σi hcount_σN hpresc ψi ψiσ ψN hψi hψiσ hψN hpin_iσ hpin_N hpin_iσi hpin_iσN
    hmatch'
  exact ⟨ψN, hψN, hpinM, hsum⟩

end Work.SSGRoute.ZDataMup
