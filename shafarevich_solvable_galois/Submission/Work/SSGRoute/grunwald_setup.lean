import Mathlib
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.grunwald_kummer_idx
import Submission.NK.UchidaKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Plumbing for the Grünwald surjectivity lemma

This file collects the elementary transport lemmas relating the decomposition group
`decomp k A ⊓ K.fixingSubgroup ≤ G_k` to the decomposition group `decomp ↥K A` of `A` over the
intermediate field `↥K` (via `IntermediateField.fixingSubgroupEquiv`), together with the
homeomorphism property of the transport, and the naturality of the Kummer index `zr` under ring
homomorphisms.

The transport lemmas are reproduced from `Submission/Work/SSGRoute/finite_openKernel_homs_decomp_kernel.lean`
(whose import closure is broken in the workspace, so it cannot be imported here).
-/

namespace Work.SSGRoute

open scoped Pointwise Topology

noncomputable section

section Transport

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω)

/-- **The group isomorphism `K.fixingSubgroup ≃* Gal(Ω/↥K)` is continuous** for the Krull
topologies. -/
lemma continuous_fixingSubgroupEquiv [FiniteDimensional k K] :
    Continuous ((IntermediateField.fixingSubgroupEquiv K).toMonoidHom :
      ↥(K.fixingSubgroup) → (Ω ≃ₐ[↥K] Ω)) := by
  let f : ↥(K.fixingSubgroup) →* (Ω ≃ₐ[↥K] Ω) :=
    (IntermediateField.fixingSubgroupEquiv K).toMonoidHom
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, f.map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff ↥K Ω] at hU
  obtain ⟨N, hNfin, hNU⟩ := hU
  haveI : FiniteDimensional ↥K N := hNfin
  have hMfin : FiniteDimensional k (N.restrictScalars k) := FiniteDimensional.trans k ↥K ↥N
  have hopen : IsOpen ((N.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen (N.restrictScalars k)
  have hmem : (Subtype.val ⁻¹' ((N.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω))) ∈
      𝓝 (1 : ↥(K.fixingSubgroup)) :=
    (hopen.preimage continuous_subtype_val).mem_nhds (by
      simp only [Set.mem_preimage]; rw [Subgroup.coe_one]; exact Subgroup.one_mem _)
  refine Filter.mem_of_superset hmem ?_
  intro x hx
  show (IntermediateField.fixingSubgroupEquiv K x) ∈ U
  apply hNU
  change (IntermediateField.fixingSubgroupEquiv K x) ∈ N.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hyM : y ∈ (N.restrictScalars k : IntermediateField k Ω) := hy
  rw [IntermediateField.mem_restrictScalars] at hyM
  have hx' : (x : Ω ≃ₐ[k] Ω) ∈ (N.restrictScalars k).fixingSubgroup := hx
  rw [IntermediateField.mem_fixingSubgroup_iff] at hx'
  exact hx' y hyM

/-- **Transport of the decomposition group** across `K.fixingSubgroup ≃* Gal(Ω/↥K)`: an element
`σ ∈ K.fixingSubgroup` stabilises `A` viewed over `↥K` if and only if it stabilises `A` viewed
over `k`. -/
lemma fixingSubgroupEquiv_mem_decomp (A : ValuationSubring Ω)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup) :
    ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ ∈ SSGRoute.decomp ↥K A) ↔
      σ ∈ SSGRoute.decomp k A := by
  have hfun : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ : Ω → Ω) = ⇑σ := rfl
  have hsmul : (IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩ : Ω ≃ₐ[↥K] Ω) • A =
      (σ : Ω ≃ₐ[k] Ω) • A := by
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
    MulAction.mem_stabilizer_iff, hsmul]

/-- **The decomposition group of `A` over `k`, intersected with `G_K`, is the decomposition group
of `A` over `K`**, via the isomorphism `K.fixingSubgroup ≃* Gal(Ω/↥K)`. -/
noncomputable def grunwaldSetupDecompEquiv (A : ValuationSubring Ω) :
    ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) ≃* ↥(SSGRoute.decomp ↥K A) where
  toFun x := ⟨(IntermediateField.fixingSubgroupEquiv K) ⟨(x : Ω ≃ₐ[k] Ω), x.2.2⟩,
    (fixingSubgroupEquiv_mem_decomp k Ω K A (x : Ω ≃ₐ[k] Ω) x.2.2).mpr x.2.1⟩
  invFun y :=
    let z : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm y.1
    ⟨(z : Ω ≃ₐ[k] Ω), ⟨(fixingSubgroupEquiv_mem_decomp k Ω K A (z : Ω ≃ₐ[k] Ω) z.2).mp
      (by rw [show (⟨(z : Ω ≃ₐ[k] Ω), z.2⟩ : ↥(K.fixingSubgroup)) = z from rfl,
            MulEquiv.apply_symm_apply]; exact y.2), z.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (IntermediateField.fixingSubgroupEquiv K) ⟨(x : Ω ≃ₐ[k] Ω), x.2.2⟩
      ⟨(y : Ω ≃ₐ[k] Ω), y.2.2⟩

/-- The isomorphism `decomp k A ⊓ K.fixingSubgroup ≃* decomp ↥K A` is a homeomorphism for the
Krull topologies. -/
lemma isHomeomorph_decompEquiv [FiniteDimensional k K] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) :
    IsHomeomorph
      (grunwaldSetupDecompEquiv k Ω K A :
        ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ↥(SSGRoute.decomp ↥K A)) := by
  have hcf := continuous_fixingSubgroupEquiv k Ω K
  have hcont : Continuous
      (grunwaldSetupDecompEquiv k Ω K A :
        ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ↥(SSGRoute.decomp ↥K A)) :=
    Continuous.subtype_mk
      (hcf.comp (Continuous.subtype_mk continuous_subtype_val (fun x => x.2.2)))
      (fun x => (fixingSubgroupEquiv_mem_decomp k Ω K A _ x.2.2).mpr x.2.1)
  haveI : CompactSpace ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
    have hclosed : IsClosed
        ((SSGRoute.decomp k A ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
          Set (Ω ≃ₐ[k] Ω)) :=
      (Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := k) (K' := Ω) A).inter
        (IntermediateField.fixingSubgroup_isClosed K)
    haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
    exact isCompact_iff_compactSpace.mp hclosed.isCompact
  haveI : T2Space ↥(SSGRoute.decomp ↥K A) := inferInstance
  exact (isHomeomorph_iff_continuous_bijective).mpr
    ⟨hcont, (grunwaldSetupDecompEquiv k Ω K A).bijective⟩

end Transport



end

/-- The action of `Gal(Ω/↥K)`, viewed as a subgroup of `G_k`, agrees with the action of `G_k`:
`(fixingSubgroupEquiv K).symm σ` acts as `σ` on places of `Ω`. -/
lemma fixingSubgroupEquiv_symm_smul (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (A : ValuationSubring Ω) (σ : Ω ≃ₐ[↥K] Ω) :
    ((IntermediateField.fixingSubgroupEquiv K).symm σ : Ω ≃ₐ[k] Ω) • A = σ • A := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl⟩

/-- `cast` along a self-equality of a type is the identity. -/
lemma cast_eq_self {α : Sort*} (h : α = α) (x : α) : cast h x = x := by
  rw [Subsingleton.elim h rfl]
  rfl

/-- `cast` along an equality of indices commutes with a dependent family of functions. -/
lemma cast_apply_cast {ι : Type*} {F : ι → Type*} {β : Type*} (c : (i : ι) → F i → β)
    {i j : ι} (hij : i = j) (x : F i) :
    c j (cast (congrArg F hij) x) = c i x := by
  subst hij
  rfl

/-- `cast` along an equality of primes commutes with the quotient projection. -/
lemma mk'_cast_adicCompletion {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsSepClosure ↥K Ω] (p : ℕ)
    {𝔭 𝔭' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)}
    (h : 𝔭 = 𝔭') (x : ((𝔭.adicCompletion ↥K))ˣ) :
    cast (congrArg (fun 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) =>
        ((𝔮.adicCompletion ↥K)ˣ ⧸ NK.UchidaKummer.ellPowSubgroup ((𝔮.adicCompletion ↥K)) p)) h)
        (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _
        (cast (congrArg (fun 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) =>
          ((𝔮.adicCompletion ↥K)ˣ)) h) x) := by
  subst h
  rfl

end Work.SSGRoute
