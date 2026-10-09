import Mathlib
import Submission.Work.SSGRoute.H9.swTwoPlacePairingTwo
import Submission.Work.SSGRoute.ZDataMup.OddForm.oPairForm_sum_attach_eq_zero_of_outside
import Submission.Work.SSGRoute.ZDataMup.oPairAtDef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The multi-place product formula in the `oPairAt` language

`Work.SSGRoute.H9.swTwoPlacePairingTwo` is the `p = 2` product formula for `T' = {Zi, ZN}`.  This
file generalises it to an *arbitrary* finite set `T'` of pairwise `K`-non-conjugate finite places:
if the Kummer cochains of `α` and `β` kill the inertia of every finite place that is not
`K`-conjugate to an element of `T'`, and `α` is killed by the involutions of `K.fixingSubgroup`,
then the local pairings of the two classes over `T'` sum to zero.

The proof is term-for-term that of `swTwoPlacePairingTwo`: the product formula
`ZDataMup.OddForm.oPairForm_sum_attach_eq_zero_of_outside` with `hout` discharged at finite places
by `H9.oTheta_ofFinite_eq_one_of_outside` and at archimedean places by `hinfα`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

theorem oPairAt_sum_attach_eq_zero_of_kills {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ)
    (T' : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T', IsFinPlace k A)
    (hTdisj : ∀ A ∈ T', ∀ B ∈ T',
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (hconfα : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ T', ¬ Work.SSGRoute.gesKConj K A B) →
      ∀ u : Ω ≃ₐ[k] Ω, IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α u = 0)
    (hconfβ : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ T', ¬ Work.SSGRoute.gesKConj K A B) →
      ∀ u : Ω ≃ₐ[k] Ω, IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β u = 0)
    (hinfα : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α c = 0) :
    ∑ A ∈ T'.attach,
      Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        A.1 (hTfin A.1 A.2)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) = 0 := by
  classical
  set ζ' : ↥K := ⟨ζ, hζK⟩ with hζ'def
  have hζ' : IsPrimitiveRoot ζ' 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- the two Kummer cochains
  have hacoc : IsCocycleOn (res k K) K.fixingSubgroup
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α) := by
    intro g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ α g hg h hh]
    rfl
  have hbcoc : IsCocycleOn (res k K) K.fixingSubgroup
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) := by
    intro g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ β g hg h hh]
    rfl
  have hαeq : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α σ =
        Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) 2 (ζ := ζ') hζ' α
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) :=
    fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ)
      (hζK := hζK) (hζ := hζ) (β := α) hσ
  have hβeq : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β σ =
        Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) 2 (ζ := ζ') hζ' β
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) :=
    fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ)
      (hζK := hζK) (hζ := hζ) (β := β) hσ
  -- `α` is positive at every real place of `↥K`
  have hnotneg : ∀ w : NumberField.InfinitePlace ↥K, ¬ Work.SSGRoute.ZDataTwo.IsNegAt w α :=
    Work.SSGRoute.ZDataTwo.not_isNegAt_of_involution_condition (k := k) (Ω := Ω) K ζ' hζ' α
      (fun c hc hc2 => by
        rw [show Work.SSGRoute.gesGalKOfFixing K c hc =
            (IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ from rfl]
        exact (hαeq c hc).symm.trans (hinfα c hc hc2))
  -- the local factors outside `T'` are trivial
  have hout : ∀ v : NK.GlobalCFT.Place ↥K,
      (∀ A ∈ T'.attach, NK.GlobalCFT.Place.ofFinite
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A.1 (hTfin A.1 A.2)) ≠ v) →
      Work.SSGRoute.ZDataMup.OddForm.oTheta (K := K) (p := 2) (k := k) (Ω := Ω)
        ζ' hζ' α β v = 1 := by
    intro v hv
    rcases v with w | 𝔭
    · -- archimedean place
      by_cases hαpow : α ∈ NK.LocalAnabelian.powSubgroup 2 ↥K
      · have hbot : Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α
            = ⊥ :=
          NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := Ω) (k := ↥K) 2
            Fact.out hζ' hαpow
        haveI : Subsingleton (↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K)
            (p := 2) α) ≃ₐ[↥K]
            ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)) := by
          rw [hbot]
          refine ⟨fun x y => AlgEquiv.ext fun z => ?_⟩
          obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp z.2
          have hz : z = algebraMap ↥K ↥(⊥ : IntermediateField ↥K Ω) c := (Subtype.ext hc).symm
          rw [hz, AlgEquiv.commutes, AlgEquiv.commutes]
        exact Subsingleton.elim _ _
      · haveI hfdL : FiniteDimensional ↥K
            ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α) :=
          Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K)
            (p := 2) ζ' hζ' α
        haveI hgalL : IsGalois ↥K
            ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α) :=
          Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
            ζ' hζ' α
        haveI hnfL : NumberField
            ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α) :=
          Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
            ζ' hζ' α
        have hmem : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
            (NK.GlobalCFT.Place.ofInfinite w) β ∈
            NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
              (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α))
              (NK.GlobalCFT.Place.ofInfinite w) :=
          Work.SSGRoute.H9.localNormSubgroup_hLevel_ofInfinite_of_not_isNegAt (K := K) (k := k)
            (Ω := Ω) ζ' hζ' α β hαpow hnotneg w
        unfold Work.SSGRoute.ZDataMup.OddForm.oTheta
        exact (Work.SSGRoute.ZDataMup.oddArtin_onePlace (K := K)
          (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)
          (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isMulCommutative (Ω := Ω) (K := K) ζ' hζ' α)
          (NK.GlobalCFT.Place.ofInfinite w)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
            (NK.GlobalCFT.Place.ofInfinite w) β)).mpr hmem
    · -- finite place
      refine Work.SSGRoute.H9.oTheta_ofFinite_eq_one_of_outside (p := 2) (K := K) (k := k) (Ω := Ω)
        ζ' hζ' _ _ α β hαeq hβeq T' hTfin ?_ 𝔭 hv
      intro B hB hnc σ hσI
      refine ⟨?_, ?_⟩
      · exact hconfα B hB (fun A hA hc =>
          hnc A hA ((Work.SSGRoute.H9.gesKConj_iff_smul_form (K := K) A B).mp hc)) σ hσI
      · exact hconfβ B hB (fun A hA hc =>
          hnc A hA ((Work.SSGRoute.H9.gesKConj_iff_smul_form (K := K) A B).mp hc)) σ hσI
  -- the product formula over `T'`
  have hsum : ∑ A ∈ T'.attach,
      Work.SSGRoute.ZDataMup.OddForm.oPairForm (K := K) (p := 2) (k := k) (Ω := Ω) ζ' hζ'
        (hTfin A.1 A.2)
        (Work.SSGRoute.toClass 2 k Ω K (ZMod 2) (decomp k A.1 ⊓ K.fixingSubgroup)
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α))
        (Work.SSGRoute.toClass 2 k Ω K (ZMod 2) (decomp k A.1 ⊓ K.fixingSubgroup)
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)) = 0 :=
    Work.SSGRoute.ZDataMup.OddForm.oPairForm_sum_attach_eq_zero_of_outside
      (K := K) (p := 2) (k := k) (Ω := Ω) ζ' hζ'
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) α β
      hacoc (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ α)
      hbcoc (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ β)
      hαeq hβeq T' hTfin hTdisj hout
  have hpair : ∑ A ∈ T'.attach,
      Work.SSGRoute.ZDataMup.OddForm.oPairForm (K := K) (p := 2) (k := k) (Ω := Ω) ζ' hζ'
        (hTfin A.1 A.2)
        (Work.SSGRoute.toClass 2 k Ω K (ZMod 2) (decomp k A.1 ⊓ K.fixingSubgroup)
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α))
        (Work.SSGRoute.toClass 2 k Ω K (ZMod 2) (decomp k A.1 ⊓ K.fixingSubgroup)
          (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β))
      = ∑ A ∈ T'.attach,
      Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        A.1 (hTfin A.1 A.2)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) := by
    refine Finset.sum_congr rfl fun A _ => ?_
    congr 1
  rw [hpair] at hsum
  exact hsum

end Work.SSGRoute.ZDataTwo.TwoRec
