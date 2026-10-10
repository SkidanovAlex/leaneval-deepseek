import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAction
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute

open NumberField IsDedekindDomain

section FiniteAux

variable {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
  [Algebra k L] [FiniteDimensional k L] [IsGalois k L]

/-- The stabiliser of the finite place `ofFinite q` in `Gal(L/k)`. -/
noncomputable abbrev stabFin (q : HeightOneSpectrum (𝓞 L)) : Subgroup (L ≃ₐ[k] L) :=
  MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q)

theorem stabFin_eq_decompSubgroup (q : HeightOneSpectrum (𝓞 L)) :
    stabFin (k := k) q =
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := k) q := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, NK.GlobalCFT.Place.smul_ofFinite,
    NK.GlobalCFT.Place.ofFinite_inj,
    ← NK.GlobalCFT.Inclusion.globalCFT_mem_decompositionSubgroup_iff]

/-- The local automorphism attached to an element of the stabiliser of a finite place is the
canonical action of the corresponding element of the decomposition group on the completion. -/
theorem localAutHom_eq_decompToAdic (q : HeightOneSpectrum (𝓞 L))
    (σ : stabFin (k := k) q) (σ' : ↥(Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
      (K := k) q)) (h : (σ' : L ≃ₐ[k] L) = σ.1) :
    (NK.HassePrinciple.localAutHom (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q) σ :
        q.adicCompletion L ≃+* q.adicCompletion L)
      = Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion q σ' := by
  refine NK.HassePrinciple.localRingEquiv_ext_of_algebraMap
    (NK.HassePrinciple.localAut_continuous (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q) σ)
    (Commons.NumberTheory.NumberField.Completion.continuous_decompositionToAdicCompletion q σ')
    ?_
  have hmap : ∀ y : L,
      algebraMap L (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q)) y
      = { toCompletion := ↑((WithVal.equiv (HeightOneSpectrum.valuation L q)).symm y) } := by
    intro y
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp
  intro x
  have hgoal : NK.HassePrinciple.localAut (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q) σ
      (algebraMap L (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q)) x)
      = (Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion q σ')
          (algebraMap L (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q)) x) := by
    rw [NK.HassePrinciple.localAut_algebraMap]
    rw [hmap (σ.1 x), hmap x]
    rw [Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion_coe, h]
    all_goals rfl
  exact hgoal

end FiniteAux

section FiniteCase

variable {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
  [Algebra k L] [FiniteDimensional k L] [IsGalois k L]

theorem finite_case (p : ℕ) [Fact p.Prime]
    (P : HeightOneSpectrum (𝓞 k)) (q : HeightOneSpectrum (𝓞 L))
    (hqP : q.asIdeal.LiesOver P.asIdeal)
    (N : Subgroup (stabFin (k := k) q)) [N.Normal]
    [Fintype (stabFin (k := k) q ⧸ N)]
    (hcyc : IsCyclic (stabFin (k := k) q ⧸ N))
    (hcard : Nat.card (stabFin (k := k) q ⧸ N) = p) :
    ∃ a : (q.adicCompletion L)ˣ,
      (∀ σ : stabFin (k := k) q,
        NK.HassePrinciple.localUnitsEquiv (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q) σ a = a) ∧
      ¬ (∃ bb : (q.adicCompletion L)ˣ,
        (∀ n : N, NK.HassePrinciple.localUnitsEquiv (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q)
            (n : stabFin (k := k) q) bb = bb) ∧
        (∏ x : stabFin (k := k) q ⧸ N,
            NK.HassePrinciple.localUnitsEquiv (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q)
              (Quotient.out x) bb) = a) := by
  classical
  letI : Algebra (P.adicCompletion k) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra P q hqP
  haveI hFD : FiniteDimensional (P.adicCompletion k) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion P q hqP
  haveI hGal : IsGalois (P.adicCompletion k) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion P q hqP
  -- The isomorphism between the stabiliser and the local Galois group.
  let Ψ : stabFin (k := k) q ≃*
      (q.adicCompletion L ≃ₐ[P.adicCompletion k] q.adicCompletion L) :=
    (MulEquiv.subgroupCongr (stabFin_eq_decompSubgroup (k := k) (L := L) q)).trans
      (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois P q hqP)
  -- The action of the stabiliser on the completion is the Galois action.
  have hact : ∀ σ : stabFin (k := k) q,
      (NK.HassePrinciple.localAutHom (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q) σ :
          q.adicCompletion L ≃+* q.adicCompletion L) = (Ψ σ).toRingEquiv := by
    intro σ
    rw [localAutHom_eq_decompToAdic q σ
      (MulEquiv.subgroupCongr (stabFin_eq_decompSubgroup (k := k) (L := L) q) σ)
      (MulEquiv.subgroupCongr_apply _ σ)]
    apply RingEquiv.ext
    intro x
    have hfun : ⇑(Ψ σ) = ⇑(Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion
        q (MulEquiv.subgroupCongr (stabFin_eq_decompSubgroup (k := k) (L := L) q) σ)) := by
      change ⇑(((MulEquiv.subgroupCongr (stabFin_eq_decompSubgroup (k := k) (L := L) q)).trans
          (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
            P q hqP)) σ) = _
      rw [MulEquiv.trans_apply,
        Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe]
      change ⇑(Commons.NumberTheory.NumberField.Completion.decompositionToLocalGaloisFun P q hqP
        (MulEquiv.subgroupCongr (stabFin_eq_decompSubgroup (k := k) (L := L) q) σ)) = _
      rw [Commons.NumberTheory.NumberField.Completion.decompositionToLocalGaloisFun_apply]
    exact (congrFun hfun x).symm
  -- The subgroup of the local Galois group cut out by `N`, and its fixed field.
  let N' : Subgroup (q.adicCompletion L ≃ₐ[P.adicCompletion k] q.adicCompletion L) :=
    N.map Ψ.toMonoidHom
  have hN'norm : N'.Normal := by
    change (Subgroup.map Ψ.toMonoidHom N).Normal
    exact (inferInstance : N.Normal).map Ψ.toMonoidHom Ψ.surjective
  haveI : N'.Normal := hN'norm
  let E' : IntermediateField (P.adicCompletion k) (q.adicCompletion L) :=
    IntermediateField.fixedField N'
  haveI hGalE' : IsGalois (P.adicCompletion k) ↥E' :=
    IsGalois.of_fixedField_normal_subgroup N'
  let Θ : (stabFin (k := k) q ⧸ N) ≃* (↥E' ≃ₐ[P.adicCompletion k] ↥E') :=
    (QuotientGroup.congr N N' Ψ rfl).trans (IsGalois.normalAutEquivQuotient N')
  have hcardE' : Nat.card (↥E' ≃ₐ[P.adicCompletion k] ↥E') = p := by
    rw [← hcard]
    exact (Nat.card_congr Θ.toEquiv).symm
  haveI hCycE' : IsCyclic (↥E' ≃ₐ[P.adicCompletion k] ↥E') := Θ.isCyclic.mp hcyc
  -- The norm index theorem for the degree-`p` subextension `E'/F`.
  have hcardNorm : Nat.card ((P.adicCompletion k)ˣ ⧸ MonoidHom.range
      (Units.map (Algebra.norm (P.adicCompletion k) : ↥E' →* (P.adicCompletion k)))) = p :=
    (Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base
      (K := k) (Q := P) (B := P.adicCompletion k) (B₁ := ↥E')).trans hcardE'
  -- Hence the norm of `E'/F` is not surjective.
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : (P.adicCompletion k)ˣ, a₀ ∉ MonoidHom.range
      (Units.map (Algebra.norm (P.adicCompletion k) : ↥E' →* (P.adicCompletion k))) := by
    by_contra h
    push_neg at h
    have htop : MonoidHom.range
        (Units.map (Algebra.norm (P.adicCompletion k) : ↥E' →* (P.adicCompletion k))) = ⊤ :=
      MonoidHom.range_eq_top.mpr (fun a => h a)
    have h1 : Nat.card ((P.adicCompletion k)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (P.adicCompletion k) : ↥E' →* (P.adicCompletion k)))) = 1 := by
      rw [htop, ← Subgroup.index_eq_card, Subgroup.index_top]
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  refine ⟨Units.map (algebraMap (P.adicCompletion k) (q.adicCompletion L)).toMonoidHom a₀, ?_, ?_⟩
  · -- the element is fixed by the whole stabiliser
    intro σ
    apply Units.ext
    rw [NK.HassePrinciple.coe_localUnitsEquiv, hact σ]
    exact (Ψ σ).commutes a₀
  · rintro ⟨bb, hbbN, hprod⟩
    -- `bb` is fixed by `N'` and hence lies in the fixed field `E'`.
    have hfixN : ∀ n : stabFin (k := k) q, n ∈ N →
        NK.HassePrinciple.localUnitsEquiv (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q) n bb = bb :=
      fun n hn => hbbN ⟨n, hn⟩
    have hmemE' : (bb : q.adicCompletion L) ∈ E' := by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      obtain ⟨n, hn, hgn⟩ := Subgroup.mem_map.mp hg
      have h2 : (Ψ n).toRingEquiv (bb : q.adicCompletion L) = (bb : q.adicCompletion L) := by
        rw [← hact n]
        exact congrArg (fun v : (q.adicCompletion L)ˣ => (v : q.adicCompletion L)) (hfixN n hn)
      rw [← hgn]
      exact h2
    -- The unit `bb` as an element of `E'`.
    let bu : (↥E')ˣ := Units.mk0 ⟨(bb : q.adicCompletion L), hmemE'⟩ (by
      intro h; exact Units.ne_zero bb (Subtype.ext_iff.mp h))
    -- The product over the quotient is the Galois product, hence the norm.
    have hptG : ∀ g : ↥(stabFin (k := k) q),
        (((Θ (QuotientGroup.mk' N g)) bu : ↥E') : q.adicCompletion L)
          = (Ψ g).toRingEquiv (bb : q.adicCompletion L) := by
      intro g
      have hcx : (QuotientGroup.congr N N' Ψ rfl) (QuotientGroup.mk' N g)
          = QuotientGroup.mk' N' (Ψ g) := QuotientGroup.congr_mk' N N' Ψ rfl g
      have h1 : (Θ (QuotientGroup.mk' N g) : ↥E' ≃ₐ[P.adicCompletion k] ↥E')
          = AlgEquiv.restrictNormalHom E' (Ψ g) := by
        change (IsGalois.normalAutEquivQuotient N')
            ((QuotientGroup.congr N N' Ψ rfl) (QuotientGroup.mk' N g)) = _
        rw [hcx]
        exact IsGalois.normalAutEquivQuotient_apply N' (Ψ g)
      rw [h1]
      show (((AlgEquiv.restrictNormalHom E' (Ψ g)) bu : ↥E') : q.adicCompletion L) = _
      rw [AlgEquiv.restrictNormalHom_apply]
      rfl
    -- Three computations.
    let w : stabFin (k := k) q ⧸ N → (q.adicCompletion L)ˣ := fun x =>
      NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
        (NK.GlobalCFT.Place.ofFinite q) (Quotient.out x) bb
    have hii : (∏ x : stabFin (k := k) q ⧸ N, (Units.coeHom (q.adicCompletion L)) (w x))
        = (algebraMap (P.adicCompletion k) (q.adicCompletion L)) (a₀ : P.adicCompletion k) := by
      have hm : (Units.coeHom (q.adicCompletion L)) (∏ x : stabFin (k := k) q ⧸ N, w x)
          = ∏ x : stabFin (k := k) q ⧸ N, (Units.coeHom (q.adicCompletion L)) (w x) :=
        map_prod (Units.coeHom (q.adicCompletion L)) w
          (Finset.univ : Finset (stabFin (k := k) q ⧸ N))
      rw [← hm, hprod]
      rfl
    have hiii : (∏ x : stabFin (k := k) q ⧸ N, (((Θ x) bu : ↥E') : q.adicCompletion L))
        = (∏ x : stabFin (k := k) q ⧸ N, (Units.coeHom (q.adicCompletion L)) (w x)) := by
      apply Finset.prod_congr rfl
      intro x _
      have hout : QuotientGroup.mk' N (Quotient.out x) = x :=
        (QuotientGroup.mk'_apply (N := N) (Quotient.out x)).trans (QuotientGroup.out_eq' x)
      have hstep : (((Θ x) bu : ↥E') : q.adicCompletion L)
          = (((Θ (QuotientGroup.mk' N (Quotient.out x))) bu : ↥E') : q.adicCompletion L) := by
        rw [hout]
      have hwx : (Units.coeHom (q.adicCompletion L)) (w x)
          = (Ψ (Quotient.out x)).toRingEquiv (bb : q.adicCompletion L) := by
        rw [show (Units.coeHom (q.adicCompletion L)) (w x) = (w x : q.adicCompletion L) from rfl,
          show (w x : q.adicCompletion L) = NK.HassePrinciple.localAutHom (K := k) (L := L)
            (NK.GlobalCFT.Place.ofFinite q) (Quotient.out x) (bb : q.adicCompletion L) from
            NK.HassePrinciple.coe_localUnitsEquiv _ _ _,
          hact (Quotient.out x)]
      rw [hstep, hptG (Quotient.out x), hwx]
    have hgal : (∏ x : stabFin (k := k) q ⧸ N, (((Θ x) bu : ↥E') : q.adicCompletion L))
        = (∏ σ : ↥E' ≃ₐ[P.adicCompletion k] ↥E', (((σ bu : ↥E') : q.adicCompletion L))) := by
      have hthis : (∏ x : stabFin (k := k) q ⧸ N, (((Θ x) bu : ↥E') : q.adicCompletion L))
          = (∏ x : stabFin (k := k) q ⧸ N,
              (((Θ.toEquiv x : ↥E' ≃ₐ[P.adicCompletion k] ↥E') bu : ↥E') :
                q.adicCompletion L)) := rfl
      rw [hthis, Equiv.prod_comp Θ.toEquiv
        (fun σ : ↥E' ≃ₐ[P.adicCompletion k] ↥E' => (((σ bu : ↥E') : q.adicCompletion L)))]
    have hnorm : (algebraMap (P.adicCompletion k) (q.adicCompletion L))
          (Algebra.norm (P.adicCompletion k) (bu : ↥E'))
        = (∏ σ : ↥E' ≃ₐ[P.adicCompletion k] ↥E', (((σ bu : ↥E') : q.adicCompletion L))) := by
      rw [IsScalarTower.algebraMap_apply (P.adicCompletion k) ↥E' (q.adicCompletion L)
        (Algebra.norm (P.adicCompletion k) (bu : ↥E'))]
      rw [Algebra.norm_eq_prod_automorphisms]
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro σ _
      rfl
    have hkey : (algebraMap (P.adicCompletion k) (q.adicCompletion L))
          (Algebra.norm (P.adicCompletion k) (bu : ↥E'))
        = (algebraMap (P.adicCompletion k) (q.adicCompletion L)) (a₀ : P.adicCompletion k) :=
      hnorm.trans (hgal.symm.trans (hiii.trans hii))
    have hinj : Function.Injective (algebraMap (P.adicCompletion k) (q.adicCompletion L)) := by
      rw [Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra_algebraMap]
      exact Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective P q hqP
    refine ha₀ ⟨bu, ?_⟩
    apply Units.ext
    rw [Units.coe_map]
    exact hinj hkey

end FiniteCase

section InfiniteAux

variable {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
  [Algebra k L] [FiniteDimensional k L] [IsGalois k L]

noncomputable abbrev stabInf (u : NumberField.InfinitePlace L) : Subgroup (L ≃ₐ[k] L) :=
  MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u)

/-- **Complex conjugation on the completion.** At a complex infinite place `u`, the local
automorphism attached to an element of the stabiliser acting as complex conjugation is complex
conjugation under the identification `u.Completion ≃+* ℂ`. -/
theorem ringEquivComplex_localAutHom (u : NumberField.InfinitePlace L) (hu : u.IsComplex)
    (σ : stabInf (k := k) u)
    (hconj : ∀ x : L, u.embedding (σ.1 x) = starRingEnd ℂ (u.embedding x)) :
    ∀ y : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u),
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu
        (NK.HassePrinciple.localAutHom (K := k) (L := L)
          (NK.GlobalCFT.Place.ofInfinite u) σ y)
      = starRingEnd ℂ
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu y) := by
  intro y
  change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu
      (NK.HassePrinciple.localAut (K := k) (L := L) (NK.GlobalCFT.Place.ofInfinite u) σ y)
    = starRingEnd ℂ
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu y)
  have hcont1 : Continuous (fun z : u.Completion =>
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu
        (NK.HassePrinciple.localAut (K := k) (L := L)
          (NK.GlobalCFT.Place.ofInfinite u) σ z)) :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding u).continuous.comp
      (NK.HassePrinciple.localAut_continuous (K := k) (L := L)
        (NK.GlobalCFT.Place.ofInfinite u) σ)
  have hcont2 : Continuous (fun z : u.Completion =>
      starRingEnd ℂ
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu z)) :=
    Complex.continuous_conj.comp
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding u).continuous
  have key : (fun z : u.Completion =>
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu
        (NK.HassePrinciple.localAut (K := k) (L := L)
          (NK.GlobalCFT.Place.ofInfinite u) σ z))
      = fun z : u.Completion =>
      starRingEnd ℂ
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu z) := by
    apply DenseRange.equalizer
      (f := ⇑(algebraMap L u.Completion))
      (NK.GlobalCFT.Galois.denseRange_algebraMap_localField
        (NK.GlobalCFT.Place.ofInfinite u)) hcont1 hcont2
    funext x
    simp only [Function.comp_apply]
    change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu
        (NK.HassePrinciple.localAut (K := k) (L := L)
          (NK.GlobalCFT.Place.ofInfinite u) σ
          (algebraMap L (NK.GlobalCFT.Place.localField L
            (NK.GlobalCFT.Place.ofInfinite u)) x))
      = starRingEnd ℂ
          (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu
            (algebraMap L (NK.GlobalCFT.Place.localField L
              (NK.GlobalCFT.Place.ofInfinite u)) x))
    rw [NK.HassePrinciple.localAut_algebraMap]
    rw [NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    rw [NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.extensionEmbedding_coe,
      NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
    simp only [WithAbs.equiv_apply]
    exact hconj x
  simpa only [] using congrFun key y

end InfiniteAux

/-! ## Auxiliary combinatorial lemmas -/

section CombAux

theorem finset_sum_ofMul {ι : Type*} (s : Finset ι) {H : Type*} [CommMonoid H] (f : ι → H) :
    (∑ i ∈ s, Additive.ofMul (f i)) = Additive.ofMul (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ih, ← ofMul_mul]

theorem fintype_sum_ofMul {ι : Type*} [Fintype ι] {H : Type*} [CommMonoid H] (f : ι → H) :
    (∑ i, Additive.ofMul (f i)) = Additive.ofMul (∏ i, f i) :=
  finset_sum_ofMul Finset.univ f

/-- A sum over a type covered by two distinct elements is the sum of the two values. -/
theorem sum_eq_add_of_cover {α : Type*} [Fintype α] {M : Type*} [AddCommMonoid M]
    (a b : α) (hne : a ≠ b) (hcov : ∀ c : α, c = a ∨ c = b) (f : α → M) :
    (∑ c : α, f c) = f a + f b := by
  classical
  have huniv : ({a, b} : Finset α) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro c
    rcases hcov c with h | h <;> simp [h]
  rw [← huniv, Finset.sum_insert (by simp [hne]), Finset.sum_singleton]

end CombAux

/-! ## Assembly -/

section Assembly

variable {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
  [Algebra k L] [FiniteDimensional k L] [IsGalois k L]

/-- The finite-place case, in the representation-theoretic language of the target. -/
theorem finite_case_rep (p : ℕ) [Fact p.Prime]
    (P : HeightOneSpectrum (𝓞 k)) (q : HeightOneSpectrum (𝓞 L))
    (hqP : q.asIdeal.LiesOver P.asIdeal)
    (N : Subgroup (stabFin (k := k) q)) [N.Normal]
    [Fintype (stabFin (k := k) q ⧸ N)]
    (hcyc : IsCyclic (stabFin (k := k) q ⧸ N))
    (hcard : Nat.card (stabFin (k := k) q ⧸ N) = p) :
    ∃ a : NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q),
      (∀ σ : stabFin (k := k) q,
        (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q)).ρ σ a = a) ∧
      ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q),
        (∀ n : N, (NK.HassePrinciple.localUnitsRep k L
            (NK.GlobalCFT.Place.ofFinite q)).ρ (n : stabFin (k := k) q) bb = bb) ∧
        (∑ x : stabFin (k := k) q ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L
            (NK.GlobalCFT.Place.ofFinite q)).ρ (Quotient.out x) bb) = a) := by
  obtain ⟨a₀, hfix, hne⟩ := finite_case p P q hqP N hcyc hcard
  refine ⟨Additive.ofMul a₀, ?_, ?_⟩
  · intro σ
    rw [show (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q)).ρ σ
          (Additive.ofMul a₀)
        = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
            (NK.GlobalCFT.Place.ofFinite q) σ a₀) from rfl,
      hfix σ]
    rfl
  · rintro ⟨bb, hbbN, hsum⟩
    apply hne
    set u₀ : (q.adicCompletion L)ˣ :=
      Additive.toMul (show Additive ((q.adicCompletion L)ˣ) from bb) with hu₀def
    have hbb : bb = Additive.ofMul u₀ := by
      rw [hu₀def]
      exact (ofMul_toMul (show Additive ((q.adicCompletion L)ˣ) from bb)).symm
    refine ⟨u₀, ?_, ?_⟩
    · intro n
      have h := hbbN n
      rw [hbb] at h
      change Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
          (NK.GlobalCFT.Place.ofFinite q) (n : stabFin (k := k) q) u₀)
        = Additive.ofMul u₀ at h
      exact Additive.ofMul.injective h
    · have h := hsum
      rw [hbb] at h
      change (∑ x : stabFin (k := k) q ⧸ N,
          Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
            (NK.GlobalCFT.Place.ofFinite q) (Quotient.out x) u₀))
        = Additive.ofMul a₀ at h
      have hs : (∑ x : stabFin (k := k) q ⧸ N,
          Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
            (NK.GlobalCFT.Place.ofFinite q) (Quotient.out x) u₀))
          = Additive.ofMul (∏ x : stabFin (k := k) q ⧸ N,
              NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
                (NK.GlobalCFT.Place.ofFinite q) (Quotient.out x) u₀) :=
        fintype_sum_ofMul _
      rw [hs] at h
      exact Additive.ofMul.injective h

/-- The archimedean case, in the representation-theoretic language of the target. -/
theorem infinite_case_rep (p : ℕ) [Fact p.Prime] (u : NumberField.InfinitePlace L)
    (N : Subgroup (stabInf (k := k) u)) [N.Normal]
    [Fintype (stabInf (k := k) u ⧸ N)]
    (hcyc : IsCyclic (stabInf (k := k) u ⧸ N))
    (hcard : Nat.card (stabInf (k := k) u ⧸ N) = p) :
    ∃ a : NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofInfinite u),
      (∀ σ : stabInf (k := k) u,
        (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofInfinite u)).ρ σ a = a) ∧
      ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofInfinite u),
        (∀ n : N, (NK.HassePrinciple.localUnitsRep k L
            (NK.GlobalCFT.Place.ofInfinite u)).ρ (n : stabInf (k := k) u) bb = bb) ∧
        (∑ x : stabInf (k := k) u ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L
            (NK.GlobalCFT.Place.ofInfinite u)).ρ (Quotient.out x) bb) = a) := by
  classical
  have hstab : stabInf (k := k) u = MulAction.stabilizer (L ≃ₐ[k] L) u := by
    ext σ
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]
  have hcardInf : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) u) = 1 ∨
      Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) u) = 2 :=
    NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two k u
  have hcardΓ1 : Nat.card (stabInf (k := k) u) = 1 ∨ Nat.card (stabInf (k := k) u) = 2 := by
    rw [hstab]
    exact hcardInf
  have hdvd : Nat.card (stabInf (k := k) u ⧸ N) ∣ Nat.card (stabInf (k := k) u) := by
    have h := Subgroup.card_mul_index (H := N)
    rw [Subgroup.index_eq_card] at h
    exact ⟨Nat.card N, by rw [h.symm, mul_comm]⟩
  have hdvd' : p ∣ Nat.card (stabInf (k := k) u) := by
    rw [← hcard]
    exact hdvd
  have hp2 : p = 2 := by
    have hpge2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    rcases hcardΓ1 with h | h
    · rw [h] at hdvd'
      have hp1 : p = 1 := Nat.dvd_one.mp hdvd'
      omega
    · rw [h] at hdvd'
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd'
      omega
  have hΓcard : Nat.card (stabInf (k := k) u) = 2 := by
    rcases hcardΓ1 with h | h
    · rw [h] at hdvd'
      have hp1 : p = 1 := Nat.dvd_one.mp hdvd'
      omega
    · exact h
  have hNcard : Nat.card N = 1 := by
    have h := Subgroup.card_mul_index (H := N)
    rw [Subgroup.index_eq_card, hcard, hΓcard, hp2] at h
    omega
  have hNbot : N = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hsub : Subsingleton N := (Nat.card_eq_one_iff_unique.mp hNcard).1
    have h1 : (⟨x, hx⟩ : N) = ⟨1, N.one_mem⟩ := Subsingleton.elim _ _
    exact Subtype.ext_iff.mp h1
  subst hNbot
  have hquot2 : Nat.card (stabInf (k := k) u ⧸ (⊥ : Subgroup (stabInf (k := k) u))) = 2 := by
    rw [hcard, hp2]
  set y₁ : stabInf (k := k) u ⧸ (⊥ : Subgroup (stabInf (k := k) u)) :=
    QuotientGroup.mk' (⊥ : Subgroup (stabInf (k := k) u)) (1 : stabInf (k := k) u) with hy₁def
  obtain ⟨y₂, hy₂ne, hy₂all⟩ :=
    (Nat.card_eq_two_iff' (x := y₁)).mp hquot2
  obtain ⟨σ₀, hσ₀def⟩ : ∃ σ₀ : stabInf (k := k) u, Quotient.out y₂ = σ₀ := ⟨_, rfl⟩
  have hout₁ : Quotient.out y₁ = 1 := by
    have hinj : Function.Injective ⇑(QuotientGroup.mk' (⊥ : Subgroup (stabInf (k := k) u))) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk'])
    apply hinj
    rw [← hy₁def]
    exact QuotientGroup.out_eq' y₁
  have hout₂ : QuotientGroup.mk' (⊥ : Subgroup (stabInf (k := k) u)) (Quotient.out y₂) = y₂ :=
    QuotientGroup.out_eq' y₂
  have hσ₀ne1 : σ₀ ≠ 1 := by
    intro hh
    apply hy₂ne
    rw [← hout₂, hσ₀def, hh, hy₁def]
  -- The stabiliser element `σ₀` acts as complex conjugation at `u`.
  have hσ₀mem : σ₀.1 ∈ MulAction.stabilizer (L ≃ₐ[k] L) u := by
    rw [MulAction.mem_stabilizer_iff]
    have h := MulAction.mem_stabilizer_iff.mp σ₀.2
    rwa [NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj] at h
  have hIsConj : NumberField.ComplexEmbedding.IsConj (u.embedding) σ₀.1 := by
    have hiff := NumberField.InfinitePlace.mem_stabilizer_mk_iff (u.embedding) σ₀.1
    rw [NumberField.InfinitePlace.mk_embedding] at hiff
    rcases hiff.mp hσ₀mem with h1 | hc
    · exact absurd (Subtype.ext h1) hσ₀ne1
    · exact hc
  have hconj : ∀ x : L, u.embedding (σ₀.1 x) = starRingEnd ℂ (u.embedding x) := by
    intro x
    have h := RingHom.congr_fun hIsConj x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at h
    exact h.symm
  have huC : u.IsComplex := by
    rw [← NumberField.InfinitePlace.mk_embedding u, NumberField.InfinitePlace.isComplex_mk_iff]
    intro hreal
    apply hσ₀ne1
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    have h := RingHom.congr_fun hIsConj x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at h
    have h2 : (NumberField.ComplexEmbedding.conjugate (u.embedding)) x = u.embedding x :=
      RingHom.congr_fun ((NumberField.ComplexEmbedding.isReal_iff).mp hreal) x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    rw [h2] at h
    exact (u.embedding).injective h.symm
  refine ⟨Additive.ofMul ((-1 : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ)), ?_, ?_⟩
  · intro σ
    rw [show (NK.HassePrinciple.localUnitsRep k L
          (NK.GlobalCFT.Place.ofInfinite u)).ρ σ
        (Additive.ofMul (-1 : (NK.GlobalCFT.Place.localField L
          (NK.GlobalCFT.Place.ofInfinite u))ˣ))
      = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
          (NK.GlobalCFT.Place.ofInfinite u) σ (-1 : (NK.GlobalCFT.Place.localField L
            (NK.GlobalCFT.Place.ofInfinite u))ˣ)) from rfl]
    congr 1
    apply Units.ext
    rw [NK.HassePrinciple.coe_localUnitsEquiv]
    simp
  · rintro ⟨bb, hbbN, hsum⟩
    set u₀ : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ :=
      Additive.toMul (show Additive ((NK.GlobalCFT.Place.localField L
        (NK.GlobalCFT.Place.ofInfinite u))ˣ) from bb) with hu₀def
    have hsum'' : (∑ x : stabInf (k := k) u ⧸ (⊥ : Subgroup (stabInf (k := k) u)),
        (NK.HassePrinciple.localUnitsRep k L
          (NK.GlobalCFT.Place.ofInfinite u)).ρ (Quotient.out x)
            (Additive.ofMul u₀)) = Additive.ofMul ((-1 : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ)) := by
      change (∑ x : stabInf (k := k) u ⧸ (⊥ : Subgroup (stabInf (k := k) u)),
        (NK.HassePrinciple.localUnitsRep k L
          (NK.GlobalCFT.Place.ofInfinite u)).ρ (Quotient.out x) bb) = Additive.ofMul ((-1 : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ))
      exact hsum
    have hcov : ∀ c : stabInf (k := k) u ⧸ (⊥ : Subgroup (stabInf (k := k) u)),
        c = y₁ ∨ c = y₂ := by
      intro c
      by_cases hc : c = y₁
      · exact Or.inl hc
      · exact Or.inr (hy₂all c hc)
    have h1r : (NK.HassePrinciple.localUnitsRep k L
          (NK.GlobalCFT.Place.ofInfinite u)).ρ 1 (Additive.ofMul u₀)
        = Additive.ofMul u₀ := by
      rw [show (NK.HassePrinciple.localUnitsRep k L
            (NK.GlobalCFT.Place.ofInfinite u)).ρ 1 (Additive.ofMul u₀)
          = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
              (NK.GlobalCFT.Place.ofInfinite u) 1 u₀) from rfl]
      congr 1
      simpa using congrArg (fun e : ((NK.GlobalCFT.Place.localField L
          (NK.GlobalCFT.Place.ofInfinite u))ˣ ≃*
            (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ) =>
          e u₀) (NK.HassePrinciple.localUnitsEquiv_one (K := k) (L := L)
            (NK.GlobalCFT.Place.ofInfinite u))
    have hsum3 : Additive.ofMul (u₀ * NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
        (NK.GlobalCFT.Place.ofInfinite u) σ₀ u₀) = Additive.ofMul ((-1 : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ)) := by
      rw [← hsum'']
      rw [sum_eq_add_of_cover y₁ y₂ hy₂ne.symm hcov
        (fun x => (NK.HassePrinciple.localUnitsRep k L
          (NK.GlobalCFT.Place.ofInfinite u)).ρ (Quotient.out x) (Additive.ofMul u₀))]
      rw [hout₁, hσ₀def, h1r,
        show (NK.HassePrinciple.localUnitsRep k L
            (NK.GlobalCFT.Place.ofInfinite u)).ρ σ₀ (Additive.ofMul u₀)
          = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
              (NK.GlobalCFT.Place.ofInfinite u) σ₀ u₀) from rfl,
        ← ofMul_mul]
    have hmain : u₀ * NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
        (NK.GlobalCFT.Place.ofInfinite u) σ₀ u₀ = -1 := Additive.ofMul.injective hsum3
    have hE := congrArg (fun w : (NK.GlobalCFT.Place.localField L
        (NK.GlobalCFT.Place.ofInfinite u))ˣ =>
          (w : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))) hmain
    simp only [Units.val_mul, Units.val_neg, Units.val_one] at hE
    have hE' := congrArg (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex huC) hE
    simp only [map_mul, map_neg, map_one] at hE'
    rw [NK.HassePrinciple.coe_localUnitsEquiv (K := k) (L := L)
      (NK.GlobalCFT.Place.ofInfinite u) σ₀ u₀] at hE'
    rw [ringEquivComplex_localAutHom (k := k) u huC σ₀ hconj
      (u₀ : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))] at hE'
    rw [Complex.mul_conj] at hE'
    have h2 : Complex.normSq (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        huC (u₀ : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))) = -1 := by
      have := congrArg Complex.re hE'
      simpa using this
    have h3 := Complex.normSq_nonneg (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      huC (u₀ : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u)))
    linarith

/-- **Shafarevich: the norm image at a proper level is proper.** For a finite Galois extension
`L/k` of number fields, a place `w'` of `L` and a normal subgroup `N` of the decomposition group
of `w'` with cyclic quotient of prime order `p`, there is a unit of `L_{w'}` fixed by the whole
decomposition group which is not a norm over the quotiented level. -/
theorem normImage_at_level_proper (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) [N.Normal]
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)]
    (hcyc : IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N))
    (hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p) :
    ∃ a : NK.HassePrinciple.localUnitsRep k L w',
      (∀ σ : MulAction.stabilizer (L ≃ₐ[k] L) w',
        (NK.HassePrinciple.localUnitsRep k L w').ρ σ a = a) ∧
      ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
        (∀ n : N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) = a) := by
  obtain ⟨v, hv⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := L) w'
  rw [NK.GlobalCFT.Place.liesOver_iff] at hv
  rcases hv with ⟨uL, uk, h1, -, h3⟩ | ⟨q, P, h1, -, h3⟩
  · subst h1
    exact infinite_case_rep p uL N hcyc hcard
  · subst h1
    exact finite_case_rep p P q h3 N hcyc hcard

end Assembly

end Work.SSGRoute
