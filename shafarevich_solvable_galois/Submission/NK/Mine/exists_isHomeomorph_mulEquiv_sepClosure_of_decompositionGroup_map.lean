import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Connected.Separation
import Submission.NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion
import Submission.NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime
import Submission.NK.Mine.AdjoinLocalGalois

namespace NK.Mine

open scoped Topology Pointwise
open IsDedekindDomain.HeightOneSpectrum

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

/-!
# The local Galois groups of corresponding places are homeomorphic

Let `K₁`, `K₂` be number fields with separable closures `K₁'`, `K₂'`, let `𝔭`, `𝔮` be finite
primes of `K₁`, `K₂` with places `A`, `B` above them, and let `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` be a
*homeomorphic* isomorphism of absolute Galois groups which maps the decomposition group of `A`
onto the decomposition group of `B`.  This file proves that then the absolute Galois groups of
the corresponding completions are isomorphic *as topological groups*:

`∃ ψ : Gal(κ̄₁/κ₁) ≃* Gal(κ̄₂/κ₂), IsHomeomorph ψ`,  `κᵢ = (Kᵢ)_{𝔭ᵢ}`.

This is the topological form of the local correspondence at a place (Neukirch–Schmidt–Wingberg,
Chapter XII, (12.1.9)); it is what is needed to transport the local structure theory of `G_{κ}`
along the correspondence (compare `NK.PTorsionTop.GlobalTop`).

The constituents:

* `NK.Mine.adjoinLocalEquiv` — the explicit isomorphism `D_A ≃* Aut_κ(M)`, `M = κ·K'`
  (`σ ↦ σ̂|_M`), is a homeomorphism by
  `NK.Mine.isHomeomorph_adjoinLocalEquiv` (the local computation);
* `AlgEquiv.autCongr e` for an isomorphism `e : M ≃ₐ[κ] κ^sep` of separable closures — this is a
  homeomorphism for *any* such `e` (`isHomeomorph_autCongr`), because conjugation by a field
  isomorphism permutes the finite intermediate fields;
* the restriction of `ϕ` to `D_A` onto `D_B` is a homeomorphism between the closed subgroups
  (`isHomeomorph_symm`, `isHomeomorph_trans` and compactness of `D_A`).
-/

section General

variable {G H J : Type*}

/-- The inverse of a homeomorphic isomorphism of topological groups is a homeomorphism. -/
theorem isHomeomorph_symm [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (e : G ≃* H) (he : IsHomeomorph (e : G → H)) :
    IsHomeomorph ((e.symm : H ≃* G) : H → G) := by
  refine ⟨?_, ?_, e.symm.bijective⟩
  · exact (Equiv.continuous_symm_iff e.toEquiv).mpr he.isOpenMap
  · exact (Equiv.continuous_symm_iff e.symm.toEquiv).mp he.continuous

/-- The composite of homeomorphic isomorphisms of topological groups is a homeomorphism. -/
theorem isHomeomorph_trans [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    [Group J] [TopologicalSpace J] (e : G ≃* H) (f : H ≃* J)
    (he : IsHomeomorph (e : G → H)) (hf : IsHomeomorph (f : H → J)) :
    IsHomeomorph ((e.trans f : G ≃* J) : G → J) := by
  rw [show ⇑(e.trans f : G ≃* J) = ⇑f ∘ ⇑e from MulEquiv.coe_trans e f]
  exact hf.comp he

/-- A `MulEquiv` whose inverse is a homeomorphism is a homeomorphism. -/
theorem isHomeomorph_of_symm [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (e : G ≃* H) (h : IsHomeomorph ((e.symm : H ≃* G) : H → G)) :
    IsHomeomorph (e : G → H) := by
  refine ⟨?_, ?_, e.bijective⟩
  · exact (Equiv.continuous_symm_iff (e.symm).toEquiv).mpr h.isOpenMap
  · exact (Equiv.continuous_symm_iff e.toEquiv).mp h.continuous

/-- **Conjugation by an algebra isomorphism is continuous** for the Krull topologies: the
neighbourhood basis at `1` consisting of the fixing subgroups of the finite intermediate fields is
permuted by conjugation. -/
theorem continuous_autCongr {K A₁ A₂ : Type*} [Field K] [Field A₁] [Field A₂]
    [Algebra K A₁] [Algebra K A₂] (e : A₁ ≃ₐ[K] A₂) :
    Continuous (AlgEquiv.autCongr e : Gal(A₁/K) →* Gal(A₂/K)) := by
  refine continuous_of_continuousAt_one (AlgEquiv.autCongr e : Gal(A₁/K) →* Gal(A₂/K)) ?_
  rw [ContinuousAt, (AlgEquiv.autCongr e : Gal(A₁/K) →* Gal(A₂/K)).map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff K A₂] at hU
  obtain ⟨E, _hEfin, hEU⟩ := hU
  rw [krullTopology_mem_nhds_one_iff K A₁]
  refine ⟨E.map (e.symm : A₂ →ₐ[K] A₁), ?_, ?_⟩
  · exact LinearEquiv.finiteDimensional
      (IntermediateField.equivMap E (e.symm : A₂ →ₐ[K] A₁)).toLinearEquiv
  · intro g hg
    refine hEU ?_
    have hgm : ∀ y ∈ (E.map (e.symm : A₂ →ₐ[K] A₁)), g y = y :=
      (IntermediateField.mem_fixingSubgroup_iff (E.map (e.symm : A₂ →ₐ[K] A₁)) g).mp hg
    exact (IntermediateField.mem_fixingSubgroup_iff E (AlgEquiv.autCongr e g)).mpr fun y hy => by
      have h1 : g (e.symm y) = e.symm y := hgm (e.symm y) ⟨y, hy, rfl⟩
      rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply, h1,
        AlgEquiv.apply_symm_apply]

/-- **Conjugation by an isomorphism of separable closures is a homeomorphism** of the absolute
Galois groups. -/
theorem isHomeomorph_autCongr {K A₁ A₂ : Type*} [Field K] [Field A₁] [Field A₂]
    [Algebra K A₁] [Algebra K A₂] [IsGalois K A₁] [IsGalois K A₂] (e : A₁ ≃ₐ[K] A₂) :
    IsHomeomorph (AlgEquiv.autCongr e : Gal(A₁/K) → Gal(A₂/K)) :=
  (isHomeomorph_iff_continuous_bijective).mpr
    ⟨continuous_autCongr e, (AlgEquiv.autCongr e).bijective⟩

end General

section Main

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

private lemma adjoin_le_adjoin_of_subset {F E : Type*} [Field F] [Field E] [Algebra F E]
    {s t : Set E} (h : s ⊆ t) : IntermediateField.adjoin F s ≤ IntermediateField.adjoin F t :=
  IntermediateField.adjoin_le_iff.mpr (h.trans (IntermediateField.subset_adjoin F t))

noncomputable section

variable (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (A : ValuationSubring K')
  (hA : A.comap (algebraMap K K') = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
  [Algebra (p.adicCompletion K) (NK.NeukirchUchida.placeCompletion A)]
  (halg : ∀ z : p.adicCompletion K,
    algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA z)

lemma exists_finite_mem_adjoin (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K') (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    [Algebra (p.adicCompletion K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : p.adicCompletion K,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA z)
    (z : NK.NeukirchUchida.placeCompletion A)
    (hz : z ∈ NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A) :
    ∃ F : IntermediateField K K', FiniteDimensional K F ∧
      (⟨z, hz⟩ : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)) ∈
      IntermediateField.adjoin (p.adicCompletion K)
        ((fun y => NK.NeukirchUchida.coInAdjoin p A y) '' (F : Set K')) := by
  classical
  haveI : Algebra.IsAlgebraic K K' := Algebra.IsSeparable.isAlgebraic K K'
  induction hz using IntermediateField.adjoin_induction with
  | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      refine ⟨IntermediateField.adjoin K ({y} : Set K'),
        IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic y).isIntegral, ?_⟩
      exact IntermediateField.subset_adjoin _ _
        ⟨y, IntermediateField.mem_adjoin_simple_self K y, rfl⟩
  | algebraMap c =>
      refine ⟨⊥, ?_, IntermediateField.algebraMap_mem _ c⟩
      exact (LinearEquiv.finiteDimensional
        (IntermediateField.botEquiv K K').toLinearEquiv.symm)
  | add x y hx hy ihx ihy =>
      obtain ⟨F₁, h₁, hx₁⟩ := ihx
      obtain ⟨F₂, h₂, hy₂⟩ := ihy
      haveI : FiniteDimensional K F₁ := h₁
      haveI : FiniteDimensional K F₂ := h₂
      have hsub₁ : (F₁ : Set K') ⊆ ((F₁ ⊔ F₂ : IntermediateField K K') : Set K') :=
        SetLike.le_def.mp (le_sup_left : F₁ ≤ F₁ ⊔ F₂)
      have hsub₂ : (F₂ : Set K') ⊆ ((F₁ ⊔ F₂ : IntermediateField K K') : Set K') :=
        SetLike.le_def.mp (le_sup_right : F₂ ≤ F₁ ⊔ F₂)
      exact ⟨F₁ ⊔ F₂, IntermediateField.finiteDimensional_sup F₁ F₂,
        add_mem (adjoin_le_adjoin_of_subset (Set.image_mono hsub₁) hx₁)
          (adjoin_le_adjoin_of_subset (Set.image_mono hsub₂) hy₂)⟩
  | inv x hx ih =>
      obtain ⟨F, hF, hx'⟩ := ih
      exact ⟨F, hF, inv_mem hx'⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨F₁, h₁, hx₁⟩ := ihx
      obtain ⟨F₂, h₂, hy₂⟩ := ihy
      haveI : FiniteDimensional K F₁ := h₁
      haveI : FiniteDimensional K F₂ := h₂
      have hsub₁ : (F₁ : Set K') ⊆ ((F₁ ⊔ F₂ : IntermediateField K K') : Set K') :=
        SetLike.le_def.mp (le_sup_left : F₁ ≤ F₁ ⊔ F₂)
      have hsub₂ : (F₂ : Set K') ⊆ ((F₁ ⊔ F₂ : IntermediateField K K') : Set K') :=
        SetLike.le_def.mp (le_sup_right : F₂ ≤ F₁ ⊔ F₂)
      exact ⟨F₁ ⊔ F₂, IntermediateField.finiteDimensional_sup F₁ F₂,
        mul_mem (adjoin_le_adjoin_of_subset (Set.image_mono hsub₁) hx₁)
          (adjoin_le_adjoin_of_subset (Set.image_mono hsub₂) hy₂)⟩

private lemma decompositionToAdjoin_mem_fixingSubgroup_adjoin (F : IntermediateField K K')
    (σ : NK.Mine.decompositionGroupOf K K' A) (hσ : (σ : Gal(K'/K)) ∈ F.fixingSubgroup) :
    NK.NeukirchUchida.decompositionToAdjoin p A hA halg σ ∈
      (IntermediateField.adjoin (p.adicCompletion K)
        ((fun y => NK.NeukirchUchida.coInAdjoin p A y) '' (F : Set K'))).fixingSubgroup := by
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr ?_
  intro z hz
  induction hz using IntermediateField.adjoin_induction with
  | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      show NK.NeukirchUchida.decompositionToAdjoin p A hA halg σ
          (NK.NeukirchUchida.coInAdjoin p A y) = NK.NeukirchUchida.coInAdjoin p A y
      rw [NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin]
      refine Subtype.ext ?_
      rw [NK.NeukirchUchida.coe_coInAdjoin, NK.NeukirchUchida.coe_coInAdjoin,
        (IntermediateField.mem_fixingSubgroup_iff F (σ : Gal(K'/K))).mp hσ y hy]
  | algebraMap c => exact (NK.NeukirchUchida.decompositionToAdjoin p A hA halg σ).commutes c
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | inv x hx ih => rw [map_inv₀, ih]
  | mul x y hx hy ihx ihy => rw [map_mul, ihx, ihy]

private theorem continuous_decompositionToAdjoin :
    Continuous (NK.NeukirchUchida.decompositionToAdjoin p A hA halg :
      NK.Mine.decompositionGroupOf K K' A →
      (NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A ≃ₐ[p.adicCompletion K]
        NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)) := by
  refine continuous_of_continuousAt_one (adjoinLocalHom p A hA halg) ?_
  rw [ContinuousAt, (adjoinLocalHom p A hA halg).map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff (p.adicCompletion K)
    ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)] at hU
  obtain ⟨E, hEfin, hEU⟩ := hU
  haveI := hEfin
  haveI hsepM : Algebra.IsSeparable (p.adicCompletion K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A) :=
    (NK.Mine.isSepClosure_adjoinPlaceCompletion p A hA halg).separable
  haveI hsepE : Algebra.IsSeparable (p.adicCompletion K) ↥E := inferInstance
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (p.adicCompletion K) ↥E
  obtain ⟨F, hFfin, hθF⟩ := exists_finite_mem_adjoin p A hA halg
    ((θ : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)) :
      NK.NeukirchUchida.placeCompletion A)
    (θ : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)).2
  refine Filter.mem_of_superset
    (x := Subtype.val ⁻¹' (F.fixingSubgroup : Set Gal(K'/K))) ?_ ?_
  · exact ((IntermediateField.fixingSubgroup_isOpen F).preimage continuous_subtype_val).mem_nhds
      (by simp)
  · rintro x hx
    have hx1 : (x : Gal(K'/K)) ∈ F.fixingSubgroup := hx
    have hfx := decompositionToAdjoin_mem_fixingSubgroup_adjoin p A hA halg F x hx1
    have hfixθ : NK.NeukirchUchida.decompositionToAdjoin p A hA halg x
        (θ : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)) =
        (θ : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfx _ hθF
    have hEeq : IntermediateField.adjoin (p.adicCompletion K)
        ({(θ : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A))} :
          Set ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)) = E := by
      rw [← IntermediateField.lift_adjoin_simple (p.adicCompletion K) E θ, hθ,
        IntermediateField.lift_top (p.adicCompletion K) E]
    have hfin : NK.NeukirchUchida.decompositionToAdjoin p A hA halg x ∈ E.fixingSubgroup := by
      rw [← hEeq]
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr ?_
      intro z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem z hz =>
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact hfixθ
      | algebraMap c =>
          exact (NK.NeukirchUchida.decompositionToAdjoin p A hA halg x).commutes c
      | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
      | inv x hx ih => rw [map_inv₀, ih]
      | mul x y hx hy ihx ihy => rw [map_mul, ihx, ihy]
    exact hEU hfin

theorem isHomeomorph_adjoinLocalEquiv
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K p) :
    IsHomeomorph (NK.Mine.adjoinLocalEquiv p A hA halg hW :
      NK.Mine.decompositionGroupOf K K' A →
      (NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A ≃ₐ[p.adicCompletion K]
        NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)) := by
  haveI : CompactSpace ↥(NK.Mine.decompositionGroupOf K K' A) := by
    have hclosed : IsClosed
        ((NK.Mine.decompositionGroupOf K K' A : Subgroup Gal(K'/K)) : Set Gal(K'/K)) :=
      Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A
    exact isCompact_iff_compactSpace.mp hclosed.isCompact
  have hcont : Continuous (NK.NeukirchUchida.decompositionToAdjoin p A hA halg :
      NK.Mine.decompositionGroupOf K K' A →
      (NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A ≃ₐ[p.adicCompletion K]
        NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)) :=
    continuous_decompositionToAdjoin p A hA halg
  haveI hT2 : T2Space (↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A) ≃ₐ[p.adicCompletion K]
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)) := by
    haveI hsep := (NK.Mine.isSepClosure_adjoinPlaceCompletion p A hA halg).separable
    haveI hAlg : Algebra.IsAlgebraic (p.adicCompletion K)
        ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A) :=
      Algebra.IsSeparable.isAlgebraic _ _
    haveI hInt : Algebra.IsIntegral (p.adicCompletion K)
        ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A) :=
      ⟨fun x => isAlgebraic_iff_isIntegral.mp (hAlg.isAlgebraic x)⟩
    exact krullTopology_t2
  refine (isHomeomorph_iff_continuous_bijective).mpr
    ⟨?_, (NK.Mine.adjoinLocalEquiv p A hA halg hW).bijective⟩
  exact hcont.congr fun σ => (NK.Mine.adjoinLocalEquiv_apply p A hA halg hW σ).symm


end

theorem exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁') (B : ValuationSubring K₂')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭)
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔮)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      NK.Mine.decompositionGroupOf K₂ K₂' B) :
    ∃ ψ : Gal(SeparableClosure (𝔭.adicCompletion K₁)/𝔭.adicCompletion K₁) ≃*
        Gal(SeparableClosure (𝔮.adicCompletion K₂)/𝔮.adicCompletion K₂),
      IsHomeomorph ψ := by
  classical
  -- the `κ`-algebra structures on the completions of `K₁'` and `K₂'` at `A` and `B`
  letI : Algebra (𝔭.adicCompletion K₁) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hA).toAlgebra
  letI : Algebra (𝔮.adicCompletion K₂) (NK.NeukirchUchida.placeCompletion B) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔮 B hB).toAlgebra
  have hW₁ : (NK.NeukirchUchida.placeCompletionIntegers A).comap
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K₁ 𝔭 :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔭 A hA
  have hW₂ : (NK.NeukirchUchida.placeCompletionIntegers B).comap
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔮 B hB) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K₂ 𝔮 :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔮 B hB
  -- `M = κ·K'` is a separable closure of `κ` (hence Galois, in particular compact/Hausdorff)
  haveI : IsSepClosure (𝔭.adicCompletion K₁)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K₁) (K' := K₁') 𝔭 A) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion 𝔭 A hA (fun z => rfl)
  haveI : IsSepClosure (𝔮.adicCompletion K₂)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K₂) (K' := K₂') 𝔮 B) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion 𝔮 B hB (fun z => rfl)
  -- ### the homeomorphic identification of `D_A` with the local Galois group of `K₁_𝔭`
  let e₁ : NK.Mine.decompositionGroupOf K₁ K₁' A ≃*
      Gal(SeparableClosure (𝔭.adicCompletion K₁)/𝔭.adicCompletion K₁) :=
    (NK.Mine.adjoinLocalEquiv 𝔭 A hA (fun z => rfl) hW₁).trans
      (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv 𝔭 A hA (fun z => rfl)))
  have h₁ : IsHomeomorph (e₁ : NK.Mine.decompositionGroupOf K₁ K₁' A →
      Gal(SeparableClosure (𝔭.adicCompletion K₁)/𝔭.adicCompletion K₁)) :=
    isHomeomorph_trans (NK.Mine.adjoinLocalEquiv 𝔭 A hA (fun z => rfl) hW₁)
      (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv 𝔭 A hA (fun z => rfl)))
      (isHomeomorph_adjoinLocalEquiv 𝔭 A hA (fun z => rfl) hW₁)
      (isHomeomorph_autCongr (NK.Mine.adjoinSepEquiv 𝔭 A hA (fun z => rfl)))
  -- ### the homeomorphic identification of `D_B` with the local Galois group of `K₂_𝔮`
  let e₂ : NK.Mine.decompositionGroupOf K₂ K₂' B ≃*
      Gal(SeparableClosure (𝔮.adicCompletion K₂)/𝔮.adicCompletion K₂) :=
    (NK.Mine.adjoinLocalEquiv 𝔮 B hB (fun z => rfl) hW₂).trans
      (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv 𝔮 B hB (fun z => rfl)))
  have h₂ : IsHomeomorph (e₂ : NK.Mine.decompositionGroupOf K₂ K₂' B →
      Gal(SeparableClosure (𝔮.adicCompletion K₂)/𝔮.adicCompletion K₂)) :=
    isHomeomorph_trans (NK.Mine.adjoinLocalEquiv 𝔮 B hB (fun z => rfl) hW₂)
      (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv 𝔮 B hB (fun z => rfl)))
      (isHomeomorph_adjoinLocalEquiv 𝔮 B hB (fun z => rfl) hW₂)
      (isHomeomorph_autCongr (NK.Mine.adjoinSepEquiv 𝔮 B hB (fun z => rfl)))
  -- ### the isomorphism `D_A ≃* D_B` induced by `ϕ`
  let eφ : NK.Mine.decompositionGroupOf K₁ K₁' A ≃* NK.Mine.decompositionGroupOf K₂ K₂' B :=
    (Subgroup.equivMapOfInjective (NK.Mine.decompositionGroupOf K₁ K₁' A)
      (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) ϕ.injective).trans (MulEquiv.subgroupCongr hAB)
  have hφ : IsHomeomorph (eφ : NK.Mine.decompositionGroupOf K₁ K₁' A →
      NK.Mine.decompositionGroupOf K₂ K₂' B) := by
    have hclosed : IsClosed
        ((NK.Mine.decompositionGroupOf K₁ K₁' A : Subgroup Gal(K₁'/K₁)) :
          Set Gal(K₁'/K₁)) :=
      Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A
    haveI : CompactSpace (NK.Mine.decompositionGroupOf K₁ K₁' A) :=
      isCompact_iff_compactSpace.mp hclosed.isCompact
    have hcont : Continuous (eφ : NK.Mine.decompositionGroupOf K₁ K₁' A →
        NK.Mine.decompositionGroupOf K₂ K₂' B) := by
      have hdir : Continuous (fun x : NK.Mine.decompositionGroupOf K₁ K₁' A =>
          (⟨(ϕ x : Gal(K₂'/K₂)), by rw [← hAB]; exact ⟨x, x.2, rfl⟩⟩ :
            NK.Mine.decompositionGroupOf K₂ K₂' B)) :=
        Continuous.subtype_mk (hϕ.continuous.comp continuous_subtype_val) _
      refine hdir.congr fun x => ?_
      refine Subtype.ext ?_
      show (((Subgroup.equivMapOfInjective (NK.Mine.decompositionGroupOf K₁ K₁' A)
          (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) ϕ.injective).trans
          (MulEquiv.subgroupCongr hAB)) x : Gal(K₂'/K₂)) =
        (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) x
      rfl
    exact (isHomeomorph_iff_continuous_bijective).mpr ⟨hcont, eφ.bijective⟩
  refine ⟨((e₁.symm.trans eφ).trans e₂), ?_⟩
  exact isHomeomorph_trans (e₁.symm.trans eφ) e₂
    (isHomeomorph_trans e₁.symm eφ (isHomeomorph_symm e₁ h₁) hφ) h₂

end Main

end NK.Mine
