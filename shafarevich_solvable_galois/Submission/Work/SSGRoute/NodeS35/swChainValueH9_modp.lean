import Mathlib
import Submission.Work.SSGRoute.H9.swChainValueH9
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS35

theorem swChainValueH9_modp {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω]
    (hp : p ≠ 2) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (bi bN : (↥K)ˣ) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (Qi QN : ValuationSubring Ω)
    (hQifin : SSGRoute.IsFinPlace k Qi)
    (hQifin' : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K σ • Qi))
    (hQisplit : SSGRoute.IsSplitIn k K Qi)
    (hQNfin' : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K σ • QN))
    (hZiN1 : ¬ Work.SSGRoute.gesKConj K Qi (Work.SSGRoute.ZDataMup.galLift K σ • Qi))
    (hZiN1' : ¬ Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.galLift K σ • Qi) Qi)
    (hZiN3 : ¬ Work.SSGRoute.gesKConj K Qi (Work.SSGRoute.ZDataMup.galLift K σ • QN))
    (hZiN3' : ¬ Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.galLift K σ • QN) Qi)
    (hconf_i : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Qi B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi u = 0)
    (hconf_σi : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.galLift K σ • Qi) B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi) u = 0)
    (hconf_σN : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.galLift K σ • QN) B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN) u = 0)
    (hcount_i : ((FractionalIdeal.count ↥K (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qi hQifin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bi : ↥K)) : ℤ) : ZMod p) = -1)
    (hcount_σi : ((FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (Work.SSGRoute.ZDataMup.galLift K σ • Qi) hQifin')
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi : (↥K)ˣ) : ↥K)) : ℤ)
        : ZMod p) = -1)
    (hcount_σN : ((FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (Work.SSGRoute.ZDataMup.galLift K σ • QN) hQNfin')
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN : (↥K)ˣ) : ↥K)) : ℤ)
        : ZMod p) = -1)
    (hpresc : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k Qi Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • Qi = Q) →
      ∀ y ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi y
          + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN y = 0)
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) bi)]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) bi)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) bi)]
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi))]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi))]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi))]
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN))]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN))]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN))]
    (ψi ψiσ ψN : Ω ≃ₐ[k] Ω)
    (hψi : ψi ∈ SSGRoute.decomp k Qi ⊓ K.fixingSubgroup)
    (hψiσ : ψiσ ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.galLift K σ • Qi) ⊓ K.fixingSubgroup)
    (hψN : ψN ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.galLift K σ • QN) ⊓ K.fixingSubgroup)
    (hpin_iσ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) bi)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψiσ, (Subgroup.mem_inf.mp hψiσ).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) bi))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (Work.SSGRoute.ZDataMup.galLift K σ • Qi) hQifin'))
    (hpin_N : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) bi)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψN, (Subgroup.mem_inf.mp hψN).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) bi))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (Work.SSGRoute.ZDataMup.galLift K σ • QN) hQNfin'))
    (hpin_iσi : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi))
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψi, (Subgroup.mem_inf.mp hψi).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi)))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qi hQifin))
    (hpin_iσN : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN))
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψi, (Subgroup.mem_inf.mp hψi).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN)))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qi hQifin))
    (hmatch : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN ψN
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψiσ) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψN
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN ψN = 0 := by
  classical
  -- ## The two-place product formulae
  have hS1 := Work.SSGRoute.H9.swTwoPlacePairing_zero (K := K) (p := p) (k := k) (Ω := Ω) hp ζ hζ
    hζK bi (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi) Qi
    (Work.SSGRoute.ZDataMup.galLift K σ • Qi) hQifin hQifin' hZiN1 hconf_i hconf_σi
  have hS3 := Work.SSGRoute.H9.swTwoPlacePairing_zero (K := K) (p := p) (k := k) (Ω := Ω) hp ζ hζ
    hζK bi (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN) Qi
    (Work.SSGRoute.ZDataMup.galLift K σ • QN) hQifin hQNfin' hZiN3 hconf_i hconf_σN
  -- ## The four dictionary readings
  have hd1 := Work.SSGRoute.H9.swPairingValueFrob_of_kills (K := K) (p := p) (k := k) (Ω := Ω)
    ζ hζ hζK bi (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi)
    (Work.SSGRoute.ZDataMup.galLift K σ • Qi) hQifin'
    (fun u _ hI => hconf_i _ hQifin' hZiN1 u hI) ψiσ (Subgroup.mem_inf.mp hψiσ).2 hpin_iσ
  have hd5 := Work.SSGRoute.H9.swPairingValueFrob_of_kills (K := K) (p := p) (k := k) (Ω := Ω)
    ζ hζ hζK bi (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN)
    (Work.SSGRoute.ZDataMup.galLift K σ • QN) hQNfin'
    (fun u _ hI => hconf_i _ hQNfin' hZiN3 u hI) ψN (Subgroup.mem_inf.mp hψN).2 hpin_N
  have hd2 := Work.SSGRoute.H9.swPairingValueFrob_of_kills_swap (K := K) (p := p) (k := k) (Ω := Ω)
    hp ζ hζ hζK bi (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi) Qi hQifin
    (fun u _ hI => hconf_σi _ hQifin hZiN1' u hI) ψi (Subgroup.mem_inf.mp hψi).2 hpin_iσi
  have hd6 := Work.SSGRoute.H9.swPairingValueFrob_of_kills_swap (K := K) (p := p) (k := k) (Ω := Ω)
    hp ζ hζ hζK bi (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN) Qi hQifin
    (fun u _ hI => hconf_σN _ hQifin hZiN3' u hI) ψi (Subgroup.mem_inf.mp hψi).2 hpin_iσN
  -- ## (I), (III), (IV), (δ)
  -- The escape normalisations are only available modulo `p`, but the pairings see the `A`-count of
  -- an escape class through the `ℤ`-module structure of `ZMod p`, where `n • v = (n : ZMod p) * v`;
  -- hence the residue class of the count is all that the dictionary readings use.
  have hI : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi) ψi
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψiσ := by
    rw [hd1, hd2] at hS1
    simp only [zsmul_eq_mul, hcount_σi, hcount_i, neg_one_mul, neg_neg] at hS1
    exact add_neg_eq_zero.mp hS1
  have hIII : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bN) ψi
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψN := by
    rw [hd5, hd6] at hS3
    simp only [zsmul_eq_mul, hcount_σN, hcount_i, neg_one_mul, neg_neg] at hS3
    exact add_neg_eq_zero.mp hS3
  have hIV := Work.SSGRoute.H9.swPresc_conjUnit (K := K) (p := p) ζ hζ hζK bi bN σ hσ Qi hQisplit
    hpresc
  -- ## assembly
  have key : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψN
      = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψiσ := by
    have h := hIV ψi hψi
    rw [hIII] at h
    have h2 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψN
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
            (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) bi) ψi = 0 := by
      rw [add_comm]; exact h
    rw [add_eq_zero_iff_eq_neg.mp h2, hI]
  rw [hmatch, key]
  exact neg_add_cancel _

end Work.SSGRoute.NodeS35
