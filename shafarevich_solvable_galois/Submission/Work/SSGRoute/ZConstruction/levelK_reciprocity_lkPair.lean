import Mathlib
import Submission.Work.SSGRoute.ZSplit.levelK_reciprocity_baseChange
import Submission.Work.SSGRoute.ZDataMup.Defs
import Submission.Work.SSGRoute.ZSplit.levelKPieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open scoped Pointwise
open Work.SSGRoute.ZSplit
open Work.SSGRoute
open _root_.SSGRoute


set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000


/-- **`IsLevelKLocalTateSystem` and `HasLevelKReciprocity` for the transported pairing, with the
witness exposed.**  This is `Work.SSGRoute.ZSplit.levelK_reciprocity_baseChange` with its existential
witness made explicit: the level-`K` local Tate system and the level-`K` product formula hold for the
*specific* transported pairing `Work.SSGRoute.ZSplit.lkPair p k Ω K pair'` (whose value at a level-`K`
local group `H ≤ K.fixingSubgroup` is `pair' (mapFix H) (restrFun a) (restrFun b)`).

The point of exposing the witness is that the consumer
(`SSGRoute/ZConstruction/levelK_pairing_productFormula.lean`, the assembly of gate (P)) has to attach
the *unramified orthogonality* to the same pairing
(`SSGRoute/ZConstruction/unramifiedOrthogonal_lkPairTransport` is stated for `lkPair`), which is not
possible for the opaque `Classical.choose` of the existential form. -/
theorem levelK_reciprocity_lkPair (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair' : Subgroup (Ω ≃ₐ[↥K] Ω) → ((Ω ≃ₐ[↥K] Ω) → ZMod p) →
      ((Ω ≃ₐ[↥K] Ω) → ZMod p) → ZMod p)
    (hloc : Work.SSGRoute.ZDataMup.IsLocalTateSystem p ↥K Ω (⊥ : IntermediateField ↥K Ω) pair')
    (hprod : Work.SSGRoute.ZDataMup.IsProductFormula p ↥K Ω (⊥ : IntermediateField ↥K Ω) pair') :
    Work.SSGRoute.ZSplit.IsLevelKLocalTateSystem p k Ω K
        (Work.SSGRoute.ZSplit.lkPair p k Ω K pair') ∧
      Work.SSGRoute.ZSplit.HasLevelKReciprocity p k Ω K
        (Work.SSGRoute.ZSplit.lkPair p k Ω K pair') := by
  refine ⟨?_, ?_⟩
  · intro H hex
    obtain ⟨A, hAf, hH⟩ := hex
    subst hH
    have hAfK : SSGRoute.IsFinPlace ↥K A := (isFinPlace_baseChange k Ω K A).mpr hAf
    have hbox : ∃ A' : ValuationSubring Ω, SSGRoute.IsFinPlace ↥K A' ∧
        (SSGRoute.decomp ↥K A ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup)
          = SSGRoute.decomp ↥K A' ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup :=
      ⟨A, hAfK, rfl⟩
    have hcoc : ∀ (f : (Ω ≃ₐ[k] Ω) → ZMod p),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f →
        SSGRoute.IsCocycleOn (SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω))
          (SSGRoute.decomp ↥K A ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup)
          (restrFun k Ω K (ZMod p) f) := by
      intro f hf
      have h1 := (Work.SSGRoute.ZSplit.KTransport.isCocycleOn_mapFix_iff k Ω K p (SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right f
        (restrFun k Ω K (ZMod p) f) (restrFun_agree p k Ω K f)).mp hf
      rwa [mapFix_kLocalGroup k Ω K A] at h1
    have hlcf : ∀ (f : (Ω ≃ₐ[k] Ω) → ZMod p),
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f →
        SSGRoute.IsLocConstOn (SSGRoute.decomp ↥K A ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup)
          (restrFun k Ω K (ZMod p) f) := by
      intro f hf
      have h1 := (Work.SSGRoute.ZSplit.KTransport.isLocConstOn_mapFix_iff k Ω K p (SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right f
        (restrFun k Ω K (ZMod p) f) (restrFun_agree p k Ω K f)).mp hf
      rwa [mapFix_kLocalGroup k Ω K A] at h1
    have hcob : ∀ (f : (Ω ≃ₐ[k] Ω) → ZMod p),
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) f →
        SSGRoute.IsCoboundaryOn (SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω))
          (SSGRoute.decomp ↥K A ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup)
          (restrFun k Ω K (ZMod p) f) := by
      intro f hf
      have h1 := (Work.SSGRoute.ZSplit.KTransport.isCoboundaryOn_mapFix_iff k Ω K p (SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right f
        (restrFun k Ω K (ZMod p) f) (restrFun_agree p k Ω K f)).mp hf
      rwa [mapFix_kLocalGroup k Ω K A] at h1
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a a' b ha ha' hb
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨ha'1, ha'2⟩ := ha'
      obtain ⟨hb1, hb2⟩ := hb
      rw [lkPair_kLocalGroup p k Ω K pair' A (a + a') b,
        lkPair_kLocalGroup p k Ω K pair' A a b, lkPair_kLocalGroup p k Ω K pair' A a' b,
        restrFun_add p k Ω K a a']
      exact hloc.additive_left _ hbox (restrFun k Ω K (ZMod p) a) (restrFun k Ω K (ZMod p) a')
        (restrFun k Ω K (ZMod p) b) ⟨hcoc a ha1, hlcf a ha2⟩ ⟨hcoc a' ha'1, hlcf a' ha'2⟩
        ⟨hcoc b hb1, hlcf b hb2⟩
    · intro a b b' ha hb hb'
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      obtain ⟨hb'1, hb'2⟩ := hb'
      rw [lkPair_kLocalGroup p k Ω K pair' A a (b + b'),
        lkPair_kLocalGroup p k Ω K pair' A a b, lkPair_kLocalGroup p k Ω K pair' A a b',
        restrFun_add p k Ω K b b']
      exact hloc.additive_right _ hbox (restrFun k Ω K (ZMod p) a) (restrFun k Ω K (ZMod p) b)
        (restrFun k Ω K (ZMod p) b') ⟨hcoc a ha1, hlcf a ha2⟩ ⟨hcoc b hb1, hlcf b hb2⟩
        ⟨hcoc b' hb'1, hlcf b' hb'2⟩
    · intro a b ha hb hcob'
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      rw [lkPair_kLocalGroup p k Ω K pair' A a b]
      refine hloc.vanishes_coboundary _ hbox (restrFun k Ω K (ZMod p) a)
        (restrFun k Ω K (ZMod p) b) ⟨hcoc a ha1, hlcf a ha2⟩ ⟨hcoc b hb1, hlcf b hb2⟩ ?_
      rcases hcob' with hc | hc
      · exact Or.inl (hcob a hc)
      · exact Or.inr (hcob b hc)
    · intro a ha hb
      obtain ⟨ha1, ha2⟩ := ha
      have h1 : SSGRoute.IsCoboundaryOn
          (SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω))
          (SSGRoute.decomp ↥K A ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup)
          (restrFun k Ω K (ZMod p) a) := by
        refine hloc.perfect _ hbox (restrFun k Ω K (ZMod p) a) ⟨hcoc a ha1, hlcf a ha2⟩ ?_
        intro b' hb'
        obtain ⟨hb'1, hb'2⟩ := hb'
        have hcoc' : SSGRoute.IsCocycleOn (SSGRoute.res k K)
            (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (extendFun k Ω K (ZMod p) b') := by
          refine (Work.SSGRoute.ZSplit.KTransport.isCocycleOn_mapFix_iff k Ω K p (SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right
            (extendFun k Ω K (ZMod p) b') b' (fun x => (extendFun_agree p k Ω K b' x).symm)).mpr ?_
          rwa [mapFix_kLocalGroup k Ω K A]
        have hlcf' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
            (extendFun k Ω K (ZMod p) b') := by
          refine (Work.SSGRoute.ZSplit.KTransport.isLocConstOn_mapFix_iff k Ω K p (SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right
            (extendFun k Ω K (ZMod p) b') b' (fun x => (extendFun_agree p k Ω K b' x).symm)).mpr ?_
          rwa [mapFix_kLocalGroup k Ω K A]
        rw [← hb (extendFun k Ω K (ZMod p) b') ⟨hcoc', hlcf'⟩,
          lkPair_kLocalGroup p k Ω K pair' A a (extendFun k Ω K (ZMod p) b'), restrFun_extendFun]
      refine (Work.SSGRoute.ZSplit.KTransport.isCoboundaryOn_mapFix_iff k Ω K p (SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right a
        (restrFun k Ω K (ZMod p) a) (restrFun_agree p k Ω K a)).mpr ?_
      rwa [mapFix_kLocalGroup k Ω K A]
  · intro a b ha hla hb hlb T' hTfin hTconj hTunram
    have hcoca : SSGRoute.IsCocycleOn
        (SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω))
        (⊥ : IntermediateField ↥K Ω).fixingSubgroup (restrFun k Ω K (ZMod p) a) := by
      have h1 := (Work.SSGRoute.ZSplit.KTransport.isCocycleOn_mapFix_iff k Ω K p K.fixingSubgroup le_rfl a (restrFun k Ω K (ZMod p) a)
        (restrFun_agree p k Ω K a)).mp ha
      rwa [mapFix_self k Ω K] at h1
    have hlca : SSGRoute.IsLocConstOn (⊥ : IntermediateField ↥K Ω).fixingSubgroup
        (restrFun k Ω K (ZMod p) a) := by
      have h1 := (Work.SSGRoute.ZSplit.KTransport.isLocConstOn_mapFix_iff k Ω K p K.fixingSubgroup le_rfl a (restrFun k Ω K (ZMod p) a)
        (restrFun_agree p k Ω K a)).mp hla
      rwa [mapFix_self k Ω K] at h1
    have hcocb : SSGRoute.IsCocycleOn
        (SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω))
        (⊥ : IntermediateField ↥K Ω).fixingSubgroup (restrFun k Ω K (ZMod p) b) := by
      have h1 := (Work.SSGRoute.ZSplit.KTransport.isCocycleOn_mapFix_iff k Ω K p K.fixingSubgroup le_rfl b (restrFun k Ω K (ZMod p) b)
        (restrFun_agree p k Ω K b)).mp hb
      rwa [mapFix_self k Ω K] at h1
    have hlcb : SSGRoute.IsLocConstOn (⊥ : IntermediateField ↥K Ω).fixingSubgroup
        (restrFun k Ω K (ZMod p) b) := by
      have h1 := (Work.SSGRoute.ZSplit.KTransport.isLocConstOn_mapFix_iff k Ω K p K.fixingSubgroup le_rfl b (restrFun k Ω K (ZMod p) b)
        (restrFun_agree p k Ω K b)).mp hlb
      rwa [mapFix_self k Ω K] at h1
    have hTfin' : ∀ A ∈ T', SSGRoute.IsFinPlace ↥K A :=
      fun A hA => (isFinPlace_baseChange k Ω K A).mpr (hTfin A hA)
    have hTconj' : ∀ A ∈ T', ∀ B ∈ T',
        (∃ τ : Ω ≃ₐ[↥K] Ω, τ ∈ (⊥ : IntermediateField ↥K Ω).fixingSubgroup ∧
          (∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[↥K] Ω) • x ∈ A)) → A = B :=
      fun A hA B hB hc => hTconj A hA B hB ((baseBot_conj_iff k Ω K A B).mp hc)
    have hTunram' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace ↥K B →
        (∀ A ∈ T', ¬ ∃ τ : Ω ≃ₐ[↥K] Ω, τ ∈ (⊥ : IntermediateField ↥K Ω).fixingSubgroup ∧
          (∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[↥K] Ω) • x ∈ A)) →
        ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia ↥K B σ →
          restrFun k Ω K (ZMod p) a σ = 0 ∧ restrFun k Ω K (ZMod p) b σ = 0 := by
      intro B hB hnot σ hσ
      have hBk : SSGRoute.IsFinPlace k B := (isFinPlace_baseChange k Ω K B).mp hB
      have hnot' : ∀ A ∈ T', ¬ Work.SSGRoute.kConj k Ω K A B :=
        fun A hA hc => hnot A hA ((baseBot_conj_iff k Ω K A B).mpr hc)
      let u : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm σ
      have hueq : (IntermediateField.fixingSubgroupEquiv K) u = σ := by
        show (IntermediateField.fixingSubgroupEquiv K)
          ((IntermediateField.fixingSubgroupEquiv K).symm σ) = σ
        exact MulEquiv.apply_symm_apply _ σ
      have hIk : SSGRoute.IsInertia k B (u : Ω ≃ₐ[k] Ω) := by
        rw [← isInertia_baseChange k Ω K B (u : Ω ≃ₐ[k] Ω) u.2,
          show (⟨(u : Ω ≃ₐ[k] Ω), u.2⟩ : ↥(K.fixingSubgroup)) = u from rfl, hueq]
        exact hσ
      exact hTunram B hBk hnot' (u : Ω ≃ₐ[k] Ω) u.2 hIk
    have hsum : (∑ A ∈ T', lkPair p k Ω K pair' (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a b)
        = ∑ A ∈ T', pair' (SSGRoute.decomp ↥K A ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup)
            (restrFun k Ω K (ZMod p) a) (restrFun k Ω K (ZMod p) b) :=
      Finset.sum_congr rfl fun A _ => lkPair_kLocalGroup p k Ω K pair' A a b
    rw [hsum]
    exact hprod (restrFun k Ω K (ZMod p) a) (restrFun k Ω K (ZMod p) b)
      hcoca hlca hcocb hlcb T' hTfin' hTconj' hTunram'

end Work.SSGRoute.ZConstruction
