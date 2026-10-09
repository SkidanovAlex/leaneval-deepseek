import Mathlib
import Submission.Work.SSGRoute.ZSplit.levelKPieces
import Submission.Work.SSGRoute.ZSplit.KTransport.Defs
import Submission.Work.SSGRoute.ZSplit.BaseChange
import Submission.Work.SSGRoute.ZDataMup.Defs
import Submission.Work.SSGRoute.ZSplit.KTransport.isCocycleOn_mapFix_iff
import Submission.Work.SSGRoute.ZSplit.KTransport.isLocConstOn_mapFix_iff
import Submission.Work.SSGRoute.ZSplit.KTransport.isCoboundaryOn_mapFix_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` product formula as the base-`↥K` instance of the generic one

This file proves `Work.SSGRoute.ZSplit.levelK_reciprocity_baseChange` and the transport lemmas it
needs.  The static dictionary (`mapFix`, `restrFun`, `extendFun`) lives in
`ZSplit/KTransport/Defs.lean`, the place dictionary (`isFinPlace_baseChange`,
`isInertia_baseChange`, `isConjPlace_baseChange`) in `ZSplit/BaseChange.lean`, and the transport of
the three cochain predicates in `ZSplit/KTransport/isCocycleOn_mapFix_iff.lean`,
`.../isLocConstOn_mapFix_iff.lean` and `.../isCoboundaryOn_mapFix_iff.lean`.

The helper vocabulary introduced here is

* `mapFix_mem_iff`, `mapFix_kLocalGroup`, `mapFix_self` -- the image of a subgroup of `G_K`, the
  dictionary of the level-`K` local group, and `mapFix` of the whole of `G_K`;
* `restrFun_agree`, `extendFun_agree`, `restrFun_add` -- the compatibility of `restrFun` and
  `extendFun` on `G_K`, in the shape (`hag`) required by the three transport lemmas;
* `lkPair` -- the transported pairing `pair H a b = pair' (mapFix H) (restrFun a) (restrFun b)` for
  `H ≤ G_K` and `0` otherwise, with `lkPair_apply` and `lkPair_kLocalGroup`;
* `baseBot_conj_iff` -- the two spellings of level-`K` conjugacy at the trivial base extension.
-/

namespace Work.SSGRoute.ZSplit

open scoped Pointwise
open Work.SSGRoute.ZSplit
open Work.SSGRoute
open _root_.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

section Helpers

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

theorem mapFix_mem_iff (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H ≤ K.fixingSubgroup)
    (x : Ω ≃ₐ[↥K] Ω) :
    x ∈ mapFix k Ω K H hH ↔
      ((IntermediateField.fixingSubgroupEquiv K).symm x : Ω ≃ₐ[k] Ω) ∈ H := by
  rw [mapFix, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy' : (IntermediateField.fixingSubgroupEquiv K).symm x = y := by
      rw [← hyx]
      exact MulEquiv.symm_apply_apply (IntermediateField.fixingSubgroupEquiv K) y
    rw [hy']
    exact Subgroup.mem_subgroupOf.mp hy
  · intro hx
    exact ⟨(IntermediateField.fixingSubgroupEquiv K).symm x, Subgroup.mem_subgroupOf.mpr hx,
      MulEquiv.apply_symm_apply _ x⟩

/-- `mapFix` of the level-`K` local group is the `↥K`-decomposition group. -/
theorem mapFix_kLocalGroup (A : ValuationSubring Ω) :
    mapFix k Ω K (decomp k A ⊓ K.fixingSubgroup) inf_le_right
      = decomp ↥K A ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup := by
  rw [IntermediateField.fixingSubgroup_bot, inf_top_eq]
  ext x
  rw [mapFix_mem_iff k Ω K _ _ x, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : (IntermediateField.fixingSubgroupEquiv K) ((IntermediateField.fixingSubgroupEquiv K).symm x) ∈ decomp ↥K A := by
      rw [MulEquiv.apply_symm_apply]
      exact h1
    exact (fixingSubgroupEquiv_mem_decomp k Ω K A
      ((IntermediateField.fixingSubgroupEquiv K).symm x) h2).mp h2'
  · intro hx
    exact ⟨hx, ((IntermediateField.fixingSubgroupEquiv K).symm x).2⟩

/-- `mapFix` of the whole `G_K`. -/
theorem mapFix_self : mapFix k Ω K K.fixingSubgroup le_rfl = (⊥ : IntermediateField ↥K Ω).fixingSubgroup := by
  rw [mapFix, Subgroup.subgroupOf_self, IntermediateField.fixingSubgroup_bot]
  exact Subgroup.map_top_of_surjective _ (IntermediateField.fixingSubgroupEquiv K).surjective

/-- `restrFun` agrees with the original cochain on `G_K`. -/
theorem restrFun_agree (f : (Ω ≃ₐ[k] Ω) → ZMod p) :
    ∀ x : ↥(K.fixingSubgroup),
      restrFun k Ω K (ZMod p) f (IntermediateField.fixingSubgroupEquiv K x)
        = f (x : Ω ≃ₐ[k] Ω) := by
  intro x
  simp [restrFun]

/-- `restrFun` is additive. -/
theorem restrFun_add (a a' : (Ω ≃ₐ[k] Ω) → ZMod p) :
    restrFun k Ω K (ZMod p) (a + a')
      = restrFun k Ω K (ZMod p) a + restrFun k Ω K (ZMod p) a' := rfl

/-- `extendFun` agrees with the original cochain on `G_K`. -/
theorem extendFun_agree (f' : (Ω ≃ₐ[↥K] Ω) → ZMod p) :
    ∀ x : ↥(K.fixingSubgroup),
      extendFun k Ω K (ZMod p) f' (x : Ω ≃ₐ[k] Ω)
        = f' (IntermediateField.fixingSubgroupEquiv K x) := by
  intro x
  simp only [extendFun]
  rw [dif_pos x.2]

/-- The level-`K` pairing transported from a base-`↥K` pairing. -/
noncomputable def lkPair (pair' : Subgroup (Ω ≃ₐ[↥K] Ω) → ((Ω ≃ₐ[↥K] Ω) → ZMod p) →
    ((Ω ≃ₐ[↥K] Ω) → ZMod p) → ZMod p) :
    Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p :=
  fun H a b => by
    classical
    exact if hH : H ≤ K.fixingSubgroup then
      pair' (mapFix k Ω K H hH) (restrFun k Ω K (ZMod p) a) (restrFun k Ω K (ZMod p) b) else 0

theorem lkPair_apply (pair' : Subgroup (Ω ≃ₐ[↥K] Ω) → ((Ω ≃ₐ[↥K] Ω) → ZMod p) →
    ((Ω ≃ₐ[↥K] Ω) → ZMod p) → ZMod p)
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H ≤ K.fixingSubgroup) (a b : (Ω ≃ₐ[k] Ω) → ZMod p) :
    lkPair p k Ω K pair' H a b
      = pair' (mapFix k Ω K H hH) (restrFun k Ω K (ZMod p) a) (restrFun k Ω K (ZMod p) b) := by
  rw [lkPair]
  exact dif_pos hH

theorem lkPair_kLocalGroup (pair' : Subgroup (Ω ≃ₐ[↥K] Ω) → ((Ω ≃ₐ[↥K] Ω) → ZMod p) →
    ((Ω ≃ₐ[↥K] Ω) → ZMod p) → ZMod p) (A : ValuationSubring Ω) (a b : (Ω ≃ₐ[k] Ω) → ZMod p) :
    lkPair p k Ω K pair' (decomp k A ⊓ K.fixingSubgroup) a b
      = pair' (decomp ↥K A ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup)
          (restrFun k Ω K (ZMod p) a) (restrFun k Ω K (ZMod p) b) := by
  rw [lkPair_apply p k Ω K pair' _ inf_le_right a b, mapFix_kLocalGroup k Ω K A]

/-- The two spellings of level-`K` conjugacy at the trivial base extension. -/
theorem baseBot_conj_iff (A B : ValuationSubring Ω) :
    (∃ τ : Ω ≃ₐ[↥K] Ω, τ ∈ (⊥ : IntermediateField ↥K Ω).fixingSubgroup ∧
      (∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[↥K] Ω) • x ∈ A)) ↔
    Work.SSGRoute.kConj k Ω K A B := by
  have h1 : (∃ τ : Ω ≃ₐ[↥K] Ω, τ ∈ (⊥ : IntermediateField ↥K Ω).fixingSubgroup ∧
      (∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[↥K] Ω) • x ∈ A)) ↔ SSGRoute.IsConjPlace ↥K A B := by
    constructor
    · rintro ⟨τ, -, hτ⟩
      refine ⟨τ, ?_⟩
      refine SetLike.ext fun x => ?_
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact (hτ x).symm
    · rintro ⟨τ, hτ⟩
      refine ⟨τ, by rw [IntermediateField.fixingSubgroup_bot]; exact Subgroup.mem_top τ, fun x => ?_⟩
      rw [← ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hτ]
  exact h1.trans (isConjPlace_baseChange k Ω K A B).symm

end Helpers
/-- The level-`K` product formula is the instance at the base field `↥K` of the *generic* product
formula, with the trivial extension `⊥ : IntermediateField ↥K Ω` (there
`(⊥ : IntermediateField ↥K Ω).fixingSubgroup = ⊤`, so the "unramified" hypothesis of the generic
statement is exactly the level-`K` one).

This is the missing arithmetic-free link of `Work.SSGRoute.ZSplit.levelK_pairing_of_tateSystem`: its
second hypothesis `Work.SSGRoute.ZSplit.HasLevelKReciprocity` (the only non-free one, since the
local Tate system `IsLevelKLocalTateSystem` is supplied unconditionally by
`Work.SSGRoute.ZSplit.levelK_localTateSystem_exists`) is obtained from the generic
`Work.SSGRoute.ZDataMup.IsProductFormula` at the base field `↥K`, so the two lanes' product-formula
obligations (`Work.SSGRoute.ZDataMup.localTateSystem_productFormula` and this lane's) are *one*
obligation.

The transport of the local data uses `Work.SSGRoute.ZSplit.KTransport.mapFix` and
`KTransport.restrFun` (the subgroup isomorphism `K.fixingSubgroup ≃* Gal(Ω/↥K)`, the identity on
underlying functions and a homeomorphism), together with the place dictionary of
`Submission/Work/SSGRoute/ZSplit/BaseChange.lean`:

* `mapFix` of `decomp k A ⊓ K.fixingSubgroup` is `decomp ↥K A`
  (`KTransport.fixingSubgroupEquiv_mem_decomp`, `decompEquiv_fok`);
* `IsFinPlace k A ↔ IsFinPlace ↥K A` (`SSGRoute.isFinPlace_baseChange`);
* the level-`K` conjugacy `kConj k Ω K` is the `↥K`-conjugacy (`SSGRoute.isConjPlace_baseChange`);
* `IsInertia k A σ ↔ IsInertia ↥K A σ` for `σ ∈ G_K` (`SSGRoute.isInertia_baseChange`).

The cheap direction of the transport is `restrFun` (restrict a cochain on `G_k` to `G_K`); the
pairing is `pair H a b := pair' (mapFix H ·) (restrFun a) (restrFun b)` for `H ≤ G_K` and `0`
otherwise (only subgroups `≤ G_K` are ever evaluated). -/
theorem levelK_reciprocity_baseChange
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (h : ∃ pair' : Subgroup (Ω ≃ₐ[↥K] Ω) → ((Ω ≃ₐ[↥K] Ω) → ZMod p) →
        ((Ω ≃ₐ[↥K] Ω) → ZMod p) → ZMod p,
      Work.SSGRoute.ZDataMup.IsLocalTateSystem p ↥K Ω (⊥ : IntermediateField ↥K Ω) pair' ∧
      Work.SSGRoute.ZDataMup.IsProductFormula p ↥K Ω (⊥ : IntermediateField ↥K Ω) pair') :
    ∃ pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) →
        ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p,
      Work.SSGRoute.ZSplit.IsLevelKLocalTateSystem p k Ω K pair ∧
      Work.SSGRoute.ZSplit.HasLevelKReciprocity p k Ω K pair := by
  obtain ⟨pair', hloc, hprod⟩ := h
  refine ⟨lkPair p k Ω K pair', ?_, ?_⟩
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


end

end Work.SSGRoute.ZSplit
