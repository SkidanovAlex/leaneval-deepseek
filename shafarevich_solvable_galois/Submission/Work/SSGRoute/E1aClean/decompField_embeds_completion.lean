import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ExtChain.decompField_aux
import Submission.Work.SSGRoute.PT.completionFixedField
import Submission.Work.SSGRoute.place_comap_valuationSubringAtPrime

namespace Work.SSGRoute.E1aClean

open scoped Pointwise

/-- Two descriptions of the same field: the fixed field of `D_A ∩ Gal(Ω/K)` over `k` is the fixed
field of the decomposition group of `A` over `↥K`. -/
theorem mem_fixedField_decomp_inf_ker_iff (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω) (x : Ω) :
    x ∈ IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker) ↔
      x ∈ IntermediateField.fixedField (SSGRoute.decomp ↥K A) := by
  have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  have hfun_apply : ∀ τ : ↥(K.fixingSubgroup),
      (((IntermediateField.fixingSubgroupEquiv K) τ : Ω ≃ₐ[↥K] Ω) : Ω → Ω) =
        (τ : Ω ≃ₐ[k] Ω) := fun τ => rfl
  rw [hker, IntermediateField.mem_fixedField_iff, IntermediateField.mem_fixedField_iff]
  constructor
  · intro hx σ hσ
    let τ : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm σ
    have hτσ : ((IntermediateField.fixingSubgroupEquiv K) τ : Ω ≃ₐ[↥K] Ω) = σ := by
      show (IntermediateField.fixingSubgroupEquiv K)
        ((IntermediateField.fixingSubgroupEquiv K).symm σ) = σ
      rw [MulEquiv.apply_symm_apply]
    have hmem : (τ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A :=
      (fixingSubgroupEquiv_mem_decomp k Ω K A (τ : Ω ≃ₐ[k] Ω) τ.2).mp (by
        have hτeq : (⟨(τ : Ω ≃ₐ[k] Ω), τ.2⟩ : ↥(K.fixingSubgroup)) = τ := Subtype.ext rfl
        rw [hτeq, hτσ]
        exact hσ)
    have h1 : (τ : Ω ≃ₐ[k] Ω) x = x := hx (τ : Ω ≃ₐ[k] Ω) ⟨hmem, τ.2⟩
    have h2 : ((IntermediateField.fixingSubgroupEquiv K) τ : Ω ≃ₐ[↥K] Ω) x = x := by
      rw [hfun_apply τ]
      exact h1
    rwa [← hτσ]
  · intro hx σ hσ
    have hσA : σ ∈ SSGRoute.decomp k A := (Subgroup.mem_inf.mp hσ).1
    have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    have hmem : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ : Ω ≃ₐ[↥K] Ω) ∈
        SSGRoute.decomp ↥K A :=
      (fixingSubgroupEquiv_mem_decomp k Ω K A σ hσK).mpr hσA
    have h1 : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ : Ω ≃ₐ[↥K] Ω) x = x :=
      hx _ hmem
    rw [hfun_apply ⟨σ, hσK⟩] at h1
    exact h1

/-- Elementwise form of `mem_fixedField_decomp_inf_ker_iff`. -/
theorem mem_fixedField_decomp_inf_ker_iff_forall (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω) (x : Ω) :
    x ∈ IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker) ↔
      ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp ↥K A → σ x = x := by
  rw [mem_fixedField_decomp_inf_ker_iff k Ω K A x, IntermediateField.mem_fixedField_iff]

/-- An element of the algebraically closed field `Ω` fixed by the decomposition group of `A` over
`K` has its image in the completion of `Ω` at `A` inside the image of the completion of `K` at
`q`. -/
theorem coInAdjoin_mem_range_algebraMap_of_forall_fixed (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] [IsSepClosure ↥K Ω] (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAqK : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q)
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK z)
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K q)
    (x : Ω) (hx : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp ↥K A → σ x = x) :
    ∃ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) z =
        NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A x := by
  haveI hsep : IsSepClosure (q.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion q A hAqK halg
  haveI : IsGalois (q.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) := inferInstance
  refine (InfiniteGalois.mem_range_algebraMap_iff_fixed
    (NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A x)).mpr ?_
  intro f
  obtain ⟨σ, rfl⟩ := (NK.Mine.adjoinLocalEquiv q A hAqK halg hW).surjective f
  rw [NK.Mine.adjoinLocalEquiv_apply, NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin]
  exact congrArg (NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A) (hx σ.1 σ.2)

/-- A root, in a field `L`, of a nonzero polynomial over an algebraically closed field `A`
(transported along a ring hom `ρ : A →+* L`) is in the image of `ρ`. -/
theorem mem_range_of_eval_eq_zero_of_isAlgClosed {A L : Type*} [Field A] [IsAlgClosed A]
    [Field L] (ρ : A →+* L) {p : Polynomial A} (hp : p ≠ 0) {w : L}
    (hw : (p.map ρ).eval w = 0) : ∃ a : A, ρ a = w := by
  have hρinj : Function.Injective ρ := RingHom.injective ρ
  have hmap0 : p.map ρ ≠ 0 := (Polynomial.map_ne_zero_iff hρinj).mpr hp
  have hsplits : (p.map ρ).Splits := (IsAlgClosed.splits p).map ρ
  have hprod := hsplits.eval_eq_prod_roots w
  rw [hw] at hprod
  have hlc : (p.map ρ).leadingCoeff ≠ 0 := fun h =>
    hmap0 (Polynomial.leadingCoeff_eq_zero.mp h)
  have hprod0 : ((p.map ρ).roots.map (fun r => w - r)).prod = 0 := by
    rcases mul_eq_zero.mp hprod.symm with h | h
    · exact absurd h hlc
    · exact h
  obtain ⟨β, hβ, hβw⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod0)
  rw [(IsAlgClosed.splits p).roots_map ρ] at hβ
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.mp hβ
  exact ⟨a, by rw [ha]; exact (sub_eq_zero.mp hβw).symm⟩

theorem decompField_embeds_completion (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    ∃ φ : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)) →+*
        (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)),
      Function.Injective φ ∧
      (∀ x : ↥K, φ ⟨(x : Ω), Work.SSGRoute.ExtChain.le_fixedField_decomp_inf_ker k K A x.2⟩
          = algebraMap ↥K _ x) ∧
      (∀ z : NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q),
        (∃ r : Polynomial ↥(IntermediateField.fixedField
              (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
            r ≠ 0 ∧ Polynomial.eval₂ φ z r = 0) →
          ∃ x : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
            φ x = z) := by
  classical
  haveI hAlgΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hsepK : IsSepClosure ↥K Ω :=
    ⟨(inferInstance : IsSepClosure k Ω).sep_closed, inferInstance⟩
  have hAqK : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q :=
    Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  letI : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK).toAlgebra
  have halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK z := fun z => rfl
  have hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K q :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers q A hAqK
  -- ## the value map on the decomposition field
  have hval : ∀ x : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
      ∃ z : q.adicCompletion ↥K,
        algebraMap (q.adicCompletion ↥K)
            ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) z =
          NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (x : Ω) := fun x =>
    coInAdjoin_mem_range_algebraMap_of_forall_fixed k Ω K A q hAqK halg hW (x : Ω)
      ((mem_fixedField_decomp_inf_ker_iff_forall k Ω K A (x : Ω)).mp x.2)
  let γ : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)) →
      q.adicCompletion ↥K := fun x => Classical.choose (hval x)
  have γ_spec : ∀ x : ↥(IntermediateField.fixedField
        (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
      algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) (γ x) =
        NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (x : Ω) :=
    fun x => Classical.choose_spec (hval x)
  have hmap_inj : Function.Injective (algebraMap (q.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)) :=
    RingHom.injective _
  have hco_inj : Function.Injective (fun y : Ω =>
      NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A y) := by
    intro a b hab
    have h2 : NK.NeukirchUchida.placeCompletionCoe A a =
        NK.NeukirchUchida.placeCompletionCoe A b := by
      have h3 := congrArg (fun z : ↥(NK.NeukirchUchida.adjoinPlaceCompletion
        (K := ↥K) (K' := Ω) q A) => (z : NK.NeukirchUchida.placeCompletion A)) hab
      simpa only [NK.NeukirchUchida.coe_coInAdjoin] using h3
    exact RingHom.injective (NK.NeukirchUchida.placeCompletionCoe A) h2
  -- ## the ring hom
  let φ : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)) →+*
      q.adicCompletion ↥K :=
    { toFun := γ
      map_one' := by
        apply hmap_inj
        rw [γ_spec 1, map_one, IntermediateField.coe_one, NK.NeukirchUchida.coInAdjoin_one]
      map_mul' := by
        intro a b
        apply hmap_inj
        rw [map_mul, γ_spec (a * b), γ_spec a, γ_spec b, IntermediateField.coe_mul,
          NK.NeukirchUchida.coInAdjoin_mul]
      map_zero' := by
        apply hmap_inj
        rw [γ_spec 0, map_zero, IntermediateField.coe_zero, NK.NeukirchUchida.coInAdjoin_zero]
      map_add' := by
        intro a b
        apply hmap_inj
        rw [map_add, γ_spec (a + b), γ_spec a, γ_spec b, IntermediateField.coe_add,
          NK.NeukirchUchida.coInAdjoin_add] }
  have φ_spec : ∀ x : ↥(IntermediateField.fixedField
        (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
      algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) (φ x) =
        NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (x : Ω) := fun x => γ_spec x
  -- ## the compatibility of the two `↥K`-structures on the adjoined completion
  have hlink : ∀ c : ↥K,
      NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (algebraMap ↥K Ω c) =
        algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)
          (algebraMap ↥K (q.adicCompletion ↥K) c) := by
    intro c
    apply Subtype.ext
    rw [NK.NeukirchUchida.coe_coInAdjoin]
    rw [show ((algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)
          (algebraMap ↥K (q.adicCompletion ↥K) c) : ↥(NK.NeukirchUchida.adjoinPlaceCompletion
            (K := ↥K) (K' := Ω) q A)) : NK.NeukirchUchida.placeCompletion A) =
        algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)
          (algebraMap ↥K (q.adicCompletion ↥K) c) from rfl]
    rw [halg, NK.NeukirchUchida.adicCompletionToPlaceCompletion_algebraMap]
  refine ⟨φ, ?_, ?_, ?_⟩
  · -- injectivity
    intro a b hab
    have hab' : γ a = γ b := hab
    have key : NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (a : Ω) =
        NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (b : Ω) := by
      rw [← γ_spec a, ← γ_spec b, hab']
    exact Subtype.ext (hco_inj key)
  · -- the compatibility with the diagonal embedding of `K`
    intro x
    apply hmap_inj
    rw [φ_spec ⟨(x : Ω), Work.SSGRoute.ExtChain.le_fixedField_decomp_inf_ker k K A x.2⟩]
    rw [show ((⟨(x : Ω), Work.SSGRoute.ExtChain.le_fixedField_decomp_inf_ker k K A x.2⟩ :
          ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker))) : Ω)
        = algebraMap ↥K Ω x from rfl]
    exact hlink x
  · -- relative algebraic closedness of the image
    intro z ⟨r, hr0, hr⟩
    let coHom : Ω →+* ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) :=
      { toFun := fun y => NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A y
        map_one' := NK.NeukirchUchida.coInAdjoin_one q A
        map_mul' := fun a b => NK.NeukirchUchida.coInAdjoin_mul q A a b
        map_zero' := NK.NeukirchUchida.coInAdjoin_zero q A
        map_add' := fun a b => NK.NeukirchUchida.coInAdjoin_add q A a b }
    have hp0 : (r.map (algebraMap ↥(IntermediateField.fixedField
        (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)) Ω)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (f := algebraMap ↥(IntermediateField.fixedField
        (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)) Ω)
        (fun a b h => Subtype.ext h)).mpr hr0
    have hcomp : coHom.comp (algebraMap ↥(IntermediateField.fixedField
          (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)) Ω) =
        (algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)).comp φ := by
      refine RingHom.ext fun a => ?_
      exact (γ_spec a).symm
    have heval : ((r.map (algebraMap ↥(IntermediateField.fixedField
          (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)) Ω)).map coHom).eval
        (algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) z) = 0 := by
      rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, Polynomial.eval_map,
        Polynomial.eval₂_hom, ← Polynomial.eval₂_eq_eval_map, hr, map_zero]
    obtain ⟨y, hy⟩ := mem_range_of_eval_eq_zero_of_isAlgClosed coHom hp0 heval
    have hyfix : y ∈ IntermediateField.fixedField
        (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker) := by
      rw [mem_fixedField_decomp_inf_ker_iff k Ω K A y]
      exact Work.SSGRoute.PT.mem_fixedField_of_coInAdjoin_mem_range q A hAqK halg hW y ⟨z, hy⟩
    refine ⟨⟨y, hyfix⟩, ?_⟩
    apply hmap_inj
    rw [φ_spec ⟨y, hyfix⟩]
    exact hy

end Work.SSGRoute.E1aClean
