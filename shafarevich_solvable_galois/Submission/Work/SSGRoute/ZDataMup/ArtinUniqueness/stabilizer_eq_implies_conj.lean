import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The decomposition group of a finite place determines the place

Let `k` be a number field, `Ω` an algebraic (and separable) closure of `k`, `K/k` a finite Galois
subextension and `A`, `A'` finite places of `Ω` (valuation subrings over a finite prime of `k`).
The main result of this file,

`Work.SSGRoute.ZDataMup.ArtinUniqueness.stabilizer_eq_implies_conj`,

says that if the decomposition groups of `A` and `A'` cut down to the same subgroup of
`Gal(Ω/K) = K.fixingSubgroup`, then `A'` is the transport of `A` by an element of
`Gal(Ω/K)`.

In fact the hypothesis is strong enough to force `A = A'`: the decomposition group of `A` over
`K`, namely `decomp k A ⊓ K.fixingSubgroup = MulAction.stabilizer Gal(Ω/↥K) A`, is nontrivial
(`Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top`), while two
*distinct* places of a separable closure over finite primes of a number field have trivially
intersecting decomposition groups (the disjointness theorem of Neukirch–Schmidt–Wingberg,
Chapter XII (12.1.3), formalised as
`Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne`; the
arithmetic input is F. K. Schmidt's theorem that a field carrying two independent Henselian
valuations is separably closed).  Hence a place is determined by its decomposition group.

The translation between the subgroup `decomp k A ⊓ K.fixingSubgroup` of `Gal(Ω/k)` and the
decomposition group `decomp ↥K A` of `A` over `K` is provided by
`IntermediateField.fixingSubgroupEquiv K : ↥(K.fixingSubgroup) ≃* Gal(Ω/↥K)`, which acts by the
identity on the underlying functions.
-/

open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataMup.ArtinUniqueness

/-- **The decomposition group of `A` over `↥K`, transported to `Gal(Ω/k)`.**

For a place `A` of `Ω` and `σ : Ω ≃ₐ[↥K] Ω`, the element `σ` stabilises `A` over `↥K` if and only
if the corresponding element `σ₀ = (IntermediateField.fixingSubgroupEquiv K).symm σ` of
`K.fixingSubgroup ⊆ Ω ≃ₐ[k] Ω` lies in `decomp k A ⊓ K.fixingSubgroup`.

The two actions on `ValuationSubring Ω` agree because `σ` and `σ₀` are the same function. -/
lemma mem_decomp_levelK_iff_mem_inf (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (A : ValuationSubring Ω) (σ : Ω ≃ₐ[↥K] Ω) :
    σ ∈ SSGRoute.decomp ↥K A ↔
      (((IntermediateField.fixingSubgroupEquiv K).symm σ : ↥(K.fixingSubgroup)) : Ω ≃ₐ[k] Ω) ∈
        SSGRoute.decomp k A ⊓ K.fixingSubgroup := by
  have hbase : σ ∈ SSGRoute.decomp ↥K A ↔
      (((IntermediateField.fixingSubgroupEquiv K).symm σ : ↥(K.fixingSubgroup)) : Ω ≃ₐ[k] Ω) ∈
        SSGRoute.decomp k A := by
    set σ₀ : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm σ with hσ₀
    have hcoe : ((IntermediateField.fixingSubgroupEquiv K) σ₀ : Ω ≃ₐ[↥K] Ω) = σ :=
      MulEquiv.apply_symm_apply _ _
    have hfun : (((IntermediateField.fixingSubgroupEquiv K) σ₀ : Ω ≃ₐ[↥K] Ω) : Ω → Ω)
        = ⇑(σ₀ : Ω ≃ₐ[k] Ω) := rfl
    -- the two pointwise actions agree, since the two automorphisms are the same function
    have hsmul : ((IntermediateField.fixingSubgroupEquiv K) σ₀ : Ω ≃ₐ[↥K] Ω) • A
        = (σ₀ : Ω ≃ₐ[k] Ω) • A := by
      apply ValuationSubring.ext
      intro x
      rw [ValuationSubring.mem_smul_pointwise_iff_exists,
        ValuationSubring.mem_smul_pointwise_iff_exists]
      constructor
      · rintro ⟨s, hs, hx⟩
        exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hfun]⟩
      · rintro ⟨s, hs, hx⟩
        exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hfun]⟩
    rw [SSGRoute.decomp, SSGRoute.decomp, MulAction.mem_stabilizer_iff,
      MulAction.mem_stabilizer_iff, ← hcoe, hsmul]
  rw [hbase, Subgroup.mem_inf]
  exact ⟨fun hx => ⟨hx, ((IntermediateField.fixingSubgroupEquiv K).symm σ).2⟩, fun hx => hx.1⟩

/-- **A finite place is determined by its decomposition group over `K`.**

If the decomposition groups of two finite places `A`, `A'` of `Ω` cut down to the same subgroup of
`Gal(Ω/K)`, then `A' = A`.  Consequently `A'` is the transport of `A` by an element of
`Gal(Ω/K)` (the identity). -/
theorem stabilizer_eq_implies_conj (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsSepClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A A' : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hA' : SSGRoute.IsFinPlace k A')
    (h : SSGRoute.decomp k A ⊓ K.fixingSubgroup = SSGRoute.decomp k A' ⊓ K.fixingSubgroup) :
    ∃ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup ∧
      ∀ x : Ω, x ∈ A' ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A := by
  -- `↥K` is again a number field, and `Ω` is a separable closure of it
  haveI hNFK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  haveI hSepK : IsSepClosure ↥K Ω := by
    have : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    exact IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- a finite place over `k` is a finite place over `↥K`
  have hmemcomap : ∀ B : ValuationSubring Ω, B.comap (algebraMap k Ω) ≠ ⊤ →
      B.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro B hB htop
    apply hB
    refine SetLike.ext fun x => ?_
    rw [ValuationSubring.mem_comap]
    constructor
    · intro _; trivial
    · intro _
      have h1 : algebraMap k ↥K x ∈ B.comap (algebraMap ↥K Ω) := by
        rw [htop]; trivial
      rw [ValuationSubring.mem_comap] at h1
      rwa [IsScalarTower.algebraMap_apply k ↥K Ω]
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ := hmemcomap A hA
  have hAK' : A'.comap (algebraMap ↥K Ω) ≠ ⊤ := hmemcomap A' hA'
  -- transport the hypothesis to `Gal(Ω/↥K)`
  have hD : SSGRoute.decomp ↥K A = SSGRoute.decomp ↥K A' := by
    ext σ
    rw [mem_decomp_levelK_iff_mem_inf k Ω K A σ, mem_decomp_levelK_iff_mem_inf k Ω K A' σ, h]
  -- the two places have the same decomposition group over `↥K`, hence they are equal:
  -- the common group would otherwise be trivial, but decomposition groups over finite primes are
  -- nontrivial, while distinct places have trivially intersecting decomposition groups
  have hAA : A = A' := by
    by_contra hne
    have hbot : SSGRoute.decomp ↥K A ⊓ SSGRoute.decomp ↥K A' = ⊥ :=
      Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne
        hne hAK hAK'
    rw [← hD, inf_idem] at hbot
    obtain ⟨σ, hσne, hσA⟩ :=
      Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top A hAK
    have hσmem : σ ∈ SSGRoute.decomp ↥K A :=
      (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer A σ).mp hσA
    rw [hbot] at hσmem
    exact hσne (Subgroup.mem_bot.mp hσmem)
  exact ⟨1, K.fixingSubgroup.one_mem, by intro x; rw [hAA]; simp⟩

end Work.SSGRoute.ZDataMup.ArtinUniqueness
