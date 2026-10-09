import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.finite_localField_homs
import Submission.Work.SSGRoute.isOpen_map_fixingSubgroupEquiv
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.NK.Mine.AdjoinLocalGalois
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField

/-!
# Finiteness of the continuous homomorphisms of `D_A ⊓ G_K`

The target `Work.SSGRoute.finite_openKernel_homs_decomp_kernel`: for a number field `k`, an
algebraic closure `Ω`, a finite Galois `K/k`, a finite place `A` of `Ω` over `k` and a finite
`𝔽_p`-module `M`, the set of group homomorphisms

`χ : ↥(D_A ⊓ G_K) →* Multiplicative M`,  `D_A = decomp k A`,  `G_K = K.fixingSubgroup`,

whose kernel is open for the Krull topology is **finite**.

## Route

`D_A ⊓ G_K` is the decomposition group of `A` in the extension `Ω/K`; under the group isomorphism
`K.fixingSubgroup ≃* Gal(Ω/↥K)` (`IntermediateField.fixingSubgroupEquiv`) it is the decomposition
group `D_{A|K} = decomp ↥K A` of `A` over `K` (`fixingSubgroupEquiv_mem_decomp`), and the two
carry the same topology (`isHomeomorph_decompEquiv_fok`).

For the base field `K` the decomposition group is the absolute Galois group of the completion
`κ = 𝔭.adicCompletion ↥K` (`𝔭 = primeOf A hAK`), by the local/global bridge of the
Neukirch–Uchida chapter: `NK.Mine.localGaloisEquiv 𝔭 A h𝔭 halg hW : decomp ↥K A ≃* Gal(κ̄/κ)`,
which is a *homeomorphism* (`NK.Mine.isHomeomorph_adjoinLocalEquiv` plus
`NK.Mine.isHomeomorph_autCongr`).

The arithmetic input is `Work.SSGRoute.finite_localField_homs`: the continuous homomorphisms of
`Gal(κ̄/κ)` into a finite `𝔽_p`-module form a finite set.  Finiteness transports along a
homeomorphic isomorphism of topological groups (`finite_of_homeomorph_finite`).
-/

namespace Work.SSGRoute

open scoped Pointwise Topology
open Filter

/-- **Finiteness transports along a homeomorphism of topological groups.**

The set of homomorphisms of `G` into a fixed group `M` with open kernel is finite as soon as the
corresponding set for `H` is, for a homeomorphic group isomorphism `G ≃* H`.

The precomposition with `e` is a surjection from the (finite) set for `H` onto the set for `G`:
its well-definedness is continuity of `e` (`ker (f ∘ e) = e ⁻¹' ker f`), and surjectivity uses
that the inverse is an open map (`ker (χ ∘ e⁻¹) = e '' ker χ`). -/
lemma finite_of_homeomorph_finite {G H M : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] [Group M]
    (e : G ≃* H) (he : IsHomeomorph (e : G → H))
    (hfin : Finite {f : H →* M // IsOpen (f.ker : Set H)}) :
    Finite {χ : G →* M // IsOpen (χ.ker : Set G)} := by
  haveI := hfin
  let Φ : {f : H →* M // IsOpen (f.ker : Set H)} → {χ : G →* M // IsOpen (χ.ker : Set G)} :=
    fun f => ⟨f.1.comp e.toMonoidHom, by
      have hker : ((f.1.comp e.toMonoidHom).ker : Set G) = e ⁻¹' (f.1.ker : Set H) := rfl
      rw [hker]
      exact he.continuous.isOpen_preimage _ f.2⟩
  refine Finite.of_surjective Φ ?_
  intro χ
  refine ⟨⟨χ.1.comp e.symm.toMonoidHom, ?_⟩, ?_⟩
  · have hker : ((χ.1.comp e.symm.toMonoidHom).ker : Set H) = e '' (χ.1.ker : Set G) := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    rw [hker]
    exact he.isOpenMap _ χ.2
  · apply Subtype.ext
    ext x
    change χ.1 (e.symm (e x)) = χ.1 x
    rw [MulEquiv.symm_apply_apply]

section Transport

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω)

/-- **The group isomorphism `K.fixingSubgroup ≃* Gal(Ω/↥K)` is continuous** for the Krull
topologies: the preimage of the basic open subgroup `Gal(Ω/N)` (for `N/↥K` finite) contains the
basic open subgroup cut out by `N` viewed as an extension of `k`, which is finite because `K/k`
is; and the two maps have the same underlying function. -/
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

/-- The isomorphism `K.fixingSubgroup ≃* Gal(Ω/↥K)` is a homeomorphism for the Krull
topologies (a continuous bijection from a compact space to a Hausdorff space). -/
lemma isHomeomorph_fixingSubgroupEquiv [FiniteDimensional k K] [IsAlgClosure k Ω] :
    IsHomeomorph
      ((IntermediateField.fixingSubgroupEquiv K : ↥(K.fixingSubgroup) → (Ω ≃ₐ[↥K] Ω))) := by
  haveI : CompactSpace ↥(K.fixingSubgroup) := by
    have hclosed : IsClosed ((K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
      IntermediateField.fixingSubgroup_isClosed K
    haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
    exact isCompact_iff_compactSpace.mp hclosed.isCompact
  haveI : T2Space (Ω ≃ₐ[↥K] Ω) := krullTopology_t2 (K := ↥K) (L := Ω)
  exact (isHomeomorph_iff_continuous_bijective).mpr
    ⟨continuous_fixingSubgroupEquiv k Ω K, (IntermediateField.fixingSubgroupEquiv K).bijective⟩

/-- **Transport of the decomposition group** across `K.fixingSubgroup ≃* Gal(Ω/↥K)`: an element
`σ ∈ K.fixingSubgroup` stabilises `A` viewed over `↥K` if and only if it stabilises `A` viewed
over `k`.  The two actions are the same because they only depend on the underlying function. -/
lemma fixingSubgroupEquiv_mem_decomp (A : ValuationSubring Ω)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup) :
    ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ ∈ SSGRoute.decomp ↥K A) ↔
      σ ∈ SSGRoute.decomp k A := by
  have hfun : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ : Ω → Ω) = ⇑σ := rfl
  have hsmul : (IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩ : Ω ≃ₐ[↥K] Ω) • A =
      (σ : Ω ≃ₐ[k] Ω) • A := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hfun]⟩
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hfun]⟩
  rw [SSGRoute.decomp, SSGRoute.decomp, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, hsmul]

/-- **The decomposition group of `A` over `k`, intersected with `G_K`, is the decomposition group
of `A` over `K`**, via the isomorphism `K.fixingSubgroup ≃* Gal(Ω/↥K)`. -/
noncomputable def decompEquiv_fok (A : ValuationSubring Ω) :
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
lemma isHomeomorph_decompEquiv_fok [FiniteDimensional k K] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) :
    IsHomeomorph
      (decompEquiv_fok k Ω K A :
        ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ↥(SSGRoute.decomp ↥K A)) := by
  have hcf := continuous_fixingSubgroupEquiv k Ω K
  have hcont : Continuous
      (decompEquiv_fok k Ω K A :
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
    ⟨hcont, (decompEquiv_fok k Ω K A).bijective⟩

end Transport

theorem finite_openKernel_homs_decomp_kernel (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [Finite M] :
    Finite {χ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup))} := by
  -- `↥K` is a number field, and `Ω` is a separable closure of it (char. 0)
  have hNFK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  have hsep : IsSepClosure ↥K Ω := by
    have : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    exact IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- `A` is still a finite place of `Ω` over `↥K`
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro h
    apply hA
    rw [eq_top_iff]
    intro x _
    rw [ValuationSubring.mem_comap]
    have hx : algebraMap k ↥K x ∈ A.comap (algebraMap ↥K Ω) := by rw [h]; trivial
    rwa [ValuationSubring.mem_comap] at hx
  -- the prime of `↥K` below `A`, and the completion `κ = 𝔭.adicCompletion ↥K`
  let 𝔭 := Submission.NeukirchUchida.primeOf A hAK
  have h𝔭 := Submission.NeukirchUchida.primeOf_spec A hAK
  letI : Algebra (𝔭.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭).toAlgebra
  have halg : ∀ z : 𝔭.adicCompletion ↥K,
      (algebraMap (𝔭.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭 z := fun z => rfl
  have hW :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔭 A h𝔭
  haveI : IsSepClosure (𝔭.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion 𝔭 A h𝔭 halg
  -- the local identification `decomp ↥K A ≃* Gal(κ̄/κ)`, a homeomorphism
  let e₂ : ↥(SSGRoute.decomp ↥K A) ≃*
      Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K)) :=
    NK.Mine.localGaloisEquiv 𝔭 A h𝔭 halg hW
  have he₂ : IsHomeomorph
      (e₂ : ↥(SSGRoute.decomp ↥K A) →
        Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K))) :=
    NK.Mine.isHomeomorph_trans (NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW)
      (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv 𝔭 A h𝔭 halg))
      (NK.Mine.isHomeomorph_adjoinLocalEquiv 𝔭 A h𝔭 halg hW)
      (NK.Mine.isHomeomorph_autCongr (NK.Mine.adjoinSepEquiv 𝔭 A h𝔭 halg))
  -- the base change `decomp k A ⊓ G_K ≃* decomp ↥K A`, a homeomorphism
  let e₁ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) ≃* ↥(SSGRoute.decomp ↥K A) :=
    decompEquiv_fok k Ω K A
  have he₁ : IsHomeomorph
      (e₁ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ↥(SSGRoute.decomp ↥K A)) :=
    isHomeomorph_decompEquiv_fok k Ω K A
  -- the composite and the arithmetic input
  have he : IsHomeomorph
      ((e₁.trans e₂ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) ≃*
        Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K))) :
        ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
        Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K))) :=
    NK.Mine.isHomeomorph_trans e₁ e₂ he₁ he₂
  exact finite_of_homeomorph_finite (e₁.trans e₂) he (finite_localField_homs ↥K 𝔭 p M)

end Work.SSGRoute
