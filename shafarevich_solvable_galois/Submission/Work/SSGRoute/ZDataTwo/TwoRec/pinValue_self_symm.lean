import Mathlib
import Submission.Work.SSGRoute.NodeS35.swPinFamily
import Submission.Work.SSGRoute.ZDataTwo.crossedValueTwoProof
import Submission.Work.SSGRoute.H9.swChainConjDefs
import Submission.Work.SSGRoute.H9.swCount_conjUnit
import Submission.Work.SSGRoute.NodeS35.kills_inertia_conjUnit
import Submission.Work.SSGRoute.H9.swTwoPlacePairingTwo
import Submission.Work.SSGRoute.H9.oPairAt_swapTwo
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.ZDataMup.OddForm.oTheta_eq_one_of_ne_oddPrime
import Submission.Work.SSGRoute.NodeS37.oPairAt_smul_conj
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer symmetry `V_σ = V_{σ⁻¹}` of the `p = 2` escape stage

`Work.SSGRoute.NodeS35.pinValue` is the value of the Kummer cochain `χ_b` of an escape class `b` at
a Frobenius pinned at the sibling `galLift K σ • Q` of the escape prime `Q`.  This module proves the
**symmetry**

  `pinValue b (galLift K σ • Q) = pinValue b (galLift K σ⁻¹ • Q)`     (`pinValue_self_symm`)

under the three arithmetic hypotheses which the `p = 2` §4 recursion supplies for every stage: the
confinement of the class to the `K`-class of `Q` (`hconf`), the odd read-off normalisation
(`hcount`) and the vanishing at the involutions of `G_K` (`hinf`).

The proof is the `p = 2` two-place chain of Schmidt--Wingberg §4 in the `σ`-vs-`σ⁻¹` orientation:

  `χ_b(Frob_{σQ}) = ⟨χ_b, χ_{σb}⟩_{σQ}`                    [dictionary at the `σ`-sibling]
                  `= ⟨χ_{σ⁻¹b}, χ_b⟩_Q`                     [Galois invariance of the pairing,
                                                             `NodeS37.oPairAt_smul_conj`]
                  `= ⟨χ_{σ⁻¹b}, χ_b⟩_{σ⁻¹Q}`                [two-place product formula]
                  `= χ_b(Frob_{σ⁻¹Q})`.                     [dictionary at the `σ⁻¹`-sibling]

Every reading of a pairing through a Frobenius is a `pinValue`, and the two passage steps use the
twin *sibling* places `galLift K σ • Q` and `galLift K σ⁻¹ • Q`, so no comparison of Frobenius
elements of different Kummer levels is needed: the Galois invariance of the local pairing (proved in
`NodeS37/oPairAt_smul_conj.lean` through the `p = 2` norm criterion) plays the role of the "base
change" transport.
-/

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup (galLift)
open Work.SSGRoute.ZDataMup.LTRecFamHonest (hLevel hLevel_finiteDimensional hLevel_isGalois
  hLevel_numberField)
open Work.SSGRoute.ZDataMup.OddForm (oPairAt oddPrime)
open Work.SSGRoute.H9 (conjUnit swCount_conjUnit swIsUnramifiedIn_hLevel_of_kills_inertia
  swTwoPlacePairingTwo oPairAt_swapTwo)
open Work.SSGRoute.NodeS35 (exists_pinned pinValue pinValue_eq)

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- **`conjUnit` of a lifted automorphism is the image of the unit** (recorded so that the
`Units.map` form in which the transports of `H9/swCrossedValueTwoHelpers.lean` are stated can be
converted into the `conjUnit` form used by the chain). -/
private lemma conjUnit_galLift_eq_map {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (τ : K ≃ₐ[k] K) (a : (↥K)ˣ) :
    conjUnit (galLift K τ) a = Units.map τ.toRingEquiv.toMonoidHom a := by
  rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]
  rfl

/-- **Conjugating by a lift and then by the inverse lift is the identity.** -/
private lemma conjUnit_galLift_comp {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (τ : K ≃ₐ[k] K) (a : (↥K)ˣ) :
    conjUnit (galLift K τ) (conjUnit (galLift K τ⁻¹) a) = a := by
  rw [conjUnit_galLift_eq_map (K := K) τ, conjUnit_galLift_eq_map (K := K) τ⁻¹]
  ext
  simp

theorem pinValue_self_symm {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (Q : ValuationSubring Ω) (hQfin : SSGRoute.IsFinPlace k Q)
    (hQsplit : SSGRoute.IsSplitIn k K Q) (b : (↥K)ˣ)
    (hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Q B) →
      ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0)
    (hcount : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (b : ↥K))))
    (hinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b c = 0) :
    ∀ σ : K ≃ₐ[k] K,
      Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => (Q, b)) (fun _ => hQfin) 0 σ
        = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => (Q, b)) (fun _ => hQfin) 0 σ⁻¹ := by
  classical
  intro σ
  by_cases hσ : σ = 1
  · subst hσ
    rw [inv_one]
  have hσinv : σ⁻¹ ≠ 1 := fun h => hσ (inv_eq_one.mp h)
  -- ## the Kummer-level instances
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  haveI hfdb : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) b) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' b
  haveI hgalb : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) b) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' b
  haveI hnfb : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) b) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' b
  haveI hnb : Normal ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) b) := hgalb.to_normal
  -- ## the abbreviations
  set ρ : Ω ≃ₐ[k] Ω := galLift K σ with hρ
  set ρi : Ω ≃ₐ[k] Ω := galLift K σ⁻¹ with hρi
  set A : ValuationSubring Ω := ρ • Q with hAdef
  set Ai : ValuationSubring Ω := ρi • Q with hAidef
  set bt : (↥K)ˣ := conjUnit ρ b with hbt
  set bi : (↥K)ˣ := conjUnit ρi b with hbi
  haveI hfdbi : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bi) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bi
  haveI hgalbi : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bi) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bi
  haveI hnfbi : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) bi) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bi
  haveI hfdbc : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) (conjUnit ρ bi)) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' (conjUnit ρ bi)
  haveI hgalbc : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) (conjUnit ρ bi)) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' (conjUnit ρ bi)
  haveI hnfbc : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) (conjUnit ρ bi)) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' (conjUnit ρ bi)
  -- ## the two sibling places
  have hAfin : SSGRoute.IsFinPlace k A := (isFinPlace_smul_iff Q ρ).mpr hQfin
  have hAifin : SSGRoute.IsFinPlace k Ai := (isFinPlace_smul_iff Q ρi).mpr hQfin
  have hAsep : ¬ Work.SSGRoute.gesKConj K Q A :=
    Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hσ hQsplit
  have hAisep' : ¬ Work.SSGRoute.gesKConj K Q Ai :=
    Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hσinv hQsplit
  have hAisep : ¬ Work.SSGRoute.gesKConj K Ai Q :=
    fun h => hAisep' (Work.SSGRoute.H9.gesKConj_symm'' h)
  -- ## the confinement of `b`, unrestricted
  have hconf_full : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Q B) → ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0 := by
    intro B hB hnot u huI
    by_cases huK : u ∈ K.fixingSubgroup
    · exact hconf B hB hnot u huK huI
    · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem huK
  have hkillA : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k A u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0 :=
    fun u huK huI => hconf A hAfin hAsep u huK huI
  have hkillAi : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k Ai u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0 :=
    fun u huK huI => hconf Ai hAifin hAisep' u huK huI
  -- ## the transported read-off normalisations
  have hcountbt : Odd (FractionalIdeal.count ↥K
      (oddPrime (K := K) A hAfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bt : ↥K))) := by
    have h : Odd (FractionalIdeal.count ↥K
        (oddPrime (K := K) (galLift K σ • Q) hAfin)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((conjUnit (galLift K σ) b : (↥K)ˣ) : ↥K))) := by
      rw [swCount_conjUnit (K := K) b σ Q hQfin hAfin]
      exact hcount
    exact h
  have hcountbi : Odd (FractionalIdeal.count ↥K
      (oddPrime (K := K) Ai hAifin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bi : ↥K))) := by
    have h : Odd (FractionalIdeal.count ↥K
        (oddPrime (K := K) (galLift K σ⁻¹ • Q) hAifin)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((conjUnit (galLift K σ⁻¹) b : (↥K)ˣ) : ↥K))) := by
      rw [swCount_conjUnit (K := K) b σ⁻¹ Q hQfin hAifin]
      exact hcount
    exact h
  -- ## the pinned Frobenius elements
  obtain ⟨⟨ψn, hψnmem⟩, hψnpin⟩ := exists_pinned (K := K) (p := 2) ζ hζ hζK
    (fun _ => (Q, b)) 0 A hAfin hkillA
  obtain ⟨⟨ψi, hψimem⟩, hψipin⟩ := exists_pinned (K := K) (p := 2) ζ hζ hζK
    (fun _ => (Q, b)) 0 Ai hAifin hkillAi
  -- ## the confinement and involution data of the conjugate class `σ⁻¹b`
  have hconfbi : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Ai B) → ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi u = 0 := by
    have h := Work.SSGRoute.H9.CV2.hconf_conjUnit (K := K) ζ hζ hζK b σ⁻¹ Q hconf_full
    rw [← conjUnit_galLift_eq_map (K := K) σ⁻¹ b] at h
    exact h
  have hinfbi : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi c = 0 := by
    have h := Work.SSGRoute.H9.CV2.hinf_conjUnit (K := K) ζ hζ hζK b σ⁻¹ hinf
    rw [← conjUnit_galLift_eq_map (K := K) σ⁻¹ b] at h
    exact h
  -- ## step 1: the dictionary at the `σ`-sibling
  have step1 : oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ'
        A hAfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt)
      = pinValue (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b)) (fun _ => hQfin) 0 σ := by
    have hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := 2) b))
        (oddPrime (K := K) A hAfin) :=
      swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := 2) ζ hζ hζK b A hAfin hkillA
    rw [Work.SSGRoute.H9.CV2.oPairAt_eq_value_of_odd_count (K := K) ζ hζ hζK b bt A hAfin ψn
      (Subgroup.mem_inf.mp hψnmem).2 hunr hψnpin hcountbt]
    exact pinValue_eq (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b)) (fun _ => hQfin) 0 σ hσ
      ψn hψnmem hψnpin
  -- ## step 2: Galois invariance of the pairing
  have step2 : oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ'
        A hAfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt)
      = oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' Q hQfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b) := by
    have h := Work.SSGRoute.NodeS37.oPairAt_smul_conj (K := K) ζ hζ hζK bi b σ Q hQfin hAfin
    rw [hbi, hρi] at h
    rw [conjUnit_galLift_comp (K := K) σ b] at h
    exact h
  -- ## step 3: the two-place product formula for the pair `(σ⁻¹b, b)`
  have hsum := swTwoPlacePairingTwo (K := K) ζ hζ hζK bi b Ai Q hAifin hQfin hAisep
    hconfbi hconf_full hinfbi
  have step3 : oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' Q hQfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)
      = oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' Ai hAifin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b) := by
    have h' := eq_neg_of_add_eq_zero_left hsum
    rw [CharTwo.neg_eq] at h'
    exact h'.symm
  -- ## step 4: the dictionary at the `σ⁻¹`-sibling
  have step4 : oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ'
        Ai hAifin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)
      = pinValue (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b)) (fun _ => hQfin) 0 σ⁻¹ := by
    rw [oPairAt_swapTwo (K := K) ζ hζ hζK bi b Ai hAifin ψi (Subgroup.mem_inf.mp hψimem).2
      hkillAi hψipin hcountbi]
    exact pinValue_eq (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b)) (fun _ => hQfin) 0 σ⁻¹
      hσinv ψi hψimem hψipin
  -- ## the assembly
  calc pinValue (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b)) (fun _ => hQfin) 0 σ
      = oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' A hAfin
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) := step1.symm
    _ = oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' Q hQfin
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi)
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b) := step2
    _ = oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' Ai hAifin
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi)
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b) := step3
    _ = pinValue (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b)) (fun _ => hQfin) 0 σ⁻¹ := step4

end Work.SSGRoute.ZDataTwo.TwoRec
