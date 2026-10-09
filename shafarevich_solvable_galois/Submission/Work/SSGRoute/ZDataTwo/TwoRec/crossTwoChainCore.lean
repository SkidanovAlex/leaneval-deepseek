import Mathlib
import Submission.Work.SSGRoute.NodeS37.crossedValue
import Submission.Work.SSGRoute.H9.swTwoPlacePairingTwo
import Submission.Work.SSGRoute.H9.oPairAt_swapTwo
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
import Submission.Work.SSGRoute.H9.swChainConjDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-- The `conjUnit` of `galLift K τ` is the image of the unit under `τ`.  (A local copy of the
private helper of `NodeS37/crossedValue.lean`, which is needed by the chain below.) -/
private lemma conjUnit_galLift_eq_map {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (τ : K ≃ₐ[k] K) (a : (↥K)ˣ) :
    Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a
      = Units.map τ.toRingEquiv.toMonoidHom a := by
  rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]
  rfl

/-- Negation of a `ZMod 2`-element is the identity. -/
private lemma zmod_two_neg_eq_self (x : ZMod 2) : -x = x := by
  revert x
  decide

theorem crossTwoChainCore {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (bs bt a : (↥K)ˣ) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (Ps Pt : ValuationSubring Ω) (hPtfin : SSGRoute.IsFinPlace k Pt)
    (hAtfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt))
    (hAsfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps))
    (hPtAs : ¬ Work.SSGRoute.gesKConj K Pt (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps))
    (hconfα : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) B) →
      ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a τ = 0)
    (hconfβ : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Pt B) →
      ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ = 0)
    (hinfα : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a c = 0)
    (ha : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) a = bs)
    (hcounta : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (a : ↥K))))
    (hcountβ : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((Units.map σ.toRingEquiv.toMonoidHom bt : (↥K)ˣ) : ↥K))))
    (hkillbsAt : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs τ = 0)
    (hkillbtAs : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ = 0)
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a)]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a)]
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs)]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs)]
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bt)]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bt)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bt)]
    (ψt : Ω ≃ₐ[k] Ω)
    (hψt : ψt ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) ⊓ K.fixingSubgroup)
    (hpint : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψt, (Subgroup.mem_inf.mp hψt).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
          (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin))
    (ψs : Ω ≃ₐ[k] Ω)
    (hψs : ψs ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) ⊓ K.fixingSubgroup)
    (hpins : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bt)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψs, (Subgroup.mem_inf.mp hψs).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bt))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
          (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin)) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs ψt
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs := by
  classical
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- the conjugate unit `σ b_t`
  set bsig : (↥K)ˣ := Units.map σ.toRingEquiv.toMonoidHom bt with hbsigdef
  -- instances for the `hLevel` of the conjugate of `a`
  haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) a)) := by
    rw [ha]; infer_instance
  haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) a)) := by
    rw [ha]; infer_instance
  haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) a)) := by
    rw [ha]; infer_instance
  -- the odd count of `σ b_t` at the prime below `A_t`, in the `bsig` notation of the chain
  have hcountβ' : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bsig : ↥K))) := hcountβ
  -- step 1: the dictionary at `A_t`
  have hstep1 : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bsig)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs ψt :=
    Work.SSGRoute.H9.CV2.oPairAt_eq_value_of_odd_count (K := K) (k := k) (Ω := Ω)
      ζ hζ hζK bs bsig (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin ψt
      (Subgroup.mem_inf.mp hψt).2
      (Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (p := 2) ζ hζ hζK bs
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin hkillbsAt)
      hpint hcountβ'
  -- step 2: Galois invariance of the pairing
  have hstep2 : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bsig)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' Pt hPtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) := by
    have h := Work.SSGRoute.NodeS37.oPairAt_smul_conj (K := K) (k := k) (Ω := Ω)
      ζ hζ hζK a bt σ Pt hPtfin hAtfin
    rw [ha, conjUnit_galLift_eq_map, ← hbsigdef] at h
    exact h
  -- step 3: the two-place product formula at `(A_s, Pt)`
  have hstep3 : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt)
      + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' Pt hPtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) = 0 :=
    Work.SSGRoute.H9.swTwoPlacePairingTwo (K := K) (k := k) (Ω := Ω) ζ hζ hζK a bt
      (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) Pt hAsfin hPtfin
      (fun h => hPtAs (Work.SSGRoute.H9.gesKConj_symm'' h)) hconfα hconfβ hinfα
  have hstep3' : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' Pt hPtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt)
      = - Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hstep3
  -- step 4: the transpose dictionary at `A_s`
  have hstep4 : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs :=
    Work.SSGRoute.H9.oPairAt_swapTwo (K := K) (k := k) (Ω := Ω) ζ hζ hζK a bt
      (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin ψs
      (Subgroup.mem_inf.mp hψs).2 hkillbtAs hpins hcounta
  calc Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs ψt
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bsig) := hstep1.symm
    _ = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' Pt hPtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) := hstep2
    _ = - Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) := hstep3'
    _ = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs := by rw [hstep4]
    _ = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs := zmod_two_neg_eq_self _

end Work.SSGRoute.ZDataTwo.TwoRec
