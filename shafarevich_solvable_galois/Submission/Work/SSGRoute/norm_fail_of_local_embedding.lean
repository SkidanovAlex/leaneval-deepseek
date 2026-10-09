import Mathlib
import Submission.Work.SSGRoute.QLImports
import Submission.Work.SSGRoute.normImage_at_level_proper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute

noncomputable section

open NumberField IsDedekindDomain

/-- Auxiliary: the composite `(congr) ≫ (liftEquiv)` evaluated at a class `mk' N g`. -/
private lemma quotient_congr_trans_liftEquiv_mk'
    {G H H' : Type*} [Group G] [Group H] [Group H']
    (N : Subgroup G) [N.Normal] (e : G ≃* H) (N' : Subgroup H) [N'.Normal]
    (he : Subgroup.map (e : G →* H) N = N')
    (φ : H →* H') (hφ : Function.Surjective ⇑φ) (hk : N' = φ.ker) (g : G) :
    ((QuotientGroup.congr N N' e he).trans (QuotientGroup.liftEquiv N' hφ hk))
      (QuotientGroup.mk' N g) = φ (e g) := by
  rw [MulEquiv.trans_apply, QuotientGroup.congr_mk', QuotientGroup.mk'_apply,
    QuotientGroup.liftEquiv_mk]

theorem norm_fail_of_local_embedding
    (p : ℕ) [Fact p.Prime] (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (F : Type) [Field F] [Algebra (Q.adicCompletion k) F]
    [FiniteDimensional (Q.adicCompletion k) F] [IsGalois (Q.adicCompletion k) F]
    (hF : Nat.card (F ≃ₐ[Q.adicCompletion k] F) = p)
    (hne : (letI : Algebra (Q.adicCompletion k) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
      Nonempty (F →ₐ[Q.adicCompletion k] (q.adicCompletion L))))
    (a : (Q.adicCompletion k)ˣ)
    (ha : a ∉ NK.LocalReciprocity.normGroup (Q.adicCompletion k) F) :
    ∃ (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q)))
      (_ : N.Normal)
      (_ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) ⧸ N)),
      IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) ⧸ N) ∧
      Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) ⧸ N) = p ∧
      ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q),
        (∀ n : N, (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q)).ρ
          (n : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q)) bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q)).ρ
            (Quotient.out x) bb) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits
            (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite Q)
            (NK.GlobalCFT.Place.liesOver_ofFinite hq) a)) := by
  classical
  letI : Algebra (Q.adicCompletion k) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hFD : FiniteDimensional (Q.adicCompletion k) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hGal : IsGalois (Q.adicCompletion k) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  obtain ⟨φ⟩ := hne
  let E : IntermediateField (Q.adicCompletion k) (q.adicCompletion L) := φ.fieldRange
  haveI hfdE : FiniteDimensional (Q.adicCompletion k) ↥E :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange φ).toLinearEquiv
  haveI hgalE : IsGalois (Q.adicCompletion k) ↥E :=
    IsGalois.of_algEquiv (AlgHom.equivFieldRange φ)
  let Ψ : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) ≃*
      (q.adicCompletion L ≃ₐ[Q.adicCompletion k] q.adicCompletion L) :=
    (MulEquiv.subgroupCongr (stabFin_eq_decompSubgroup (k := k) (L := L) q)).trans
      (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois Q q hq)
  have hact : ∀ σ : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q),
      (NK.HassePrinciple.localAutHom (K := k) (L := L)
        (NK.GlobalCFT.Place.ofFinite q) σ : q.adicCompletion L ≃+* q.adicCompletion L)
        = (Ψ σ).toRingEquiv := by
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
            Q q hq)) σ) = _
      rw [MulEquiv.trans_apply,
        Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe]
      change ⇑(Commons.NumberTheory.NumberField.Completion.decompositionToLocalGaloisFun Q q hq
        (MulEquiv.subgroupCongr (stabFin_eq_decompSubgroup (k := k) (L := L) q) σ)) = _
      rw [Commons.NumberTheory.NumberField.Completion.decompositionToLocalGaloisFun_apply]
    exact (congrFun hfun x).symm
  let N' : Subgroup (q.adicCompletion L ≃ₐ[Q.adicCompletion k] q.adicCompletion L) :=
    E.fixingSubgroup
  haveI hN'norm : N'.Normal := inferInstance
  let N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q)) :=
    N'.comap Ψ.toMonoidHom
  haveI hNnorm : N.Normal := hN'norm.comap Ψ.toMonoidHom
  have hmap : Subgroup.map (Ψ : MulAction.stabilizer (L ≃ₐ[k] L)
      (NK.GlobalCFT.Place.ofFinite q) →*
      (q.adicCompletion L ≃ₐ[Q.adicCompletion k] q.adicCompletion L)) N = N' :=
    Subgroup.map_comap_eq_self_of_surjective Ψ.surjective N'
  have hsurj : Function.Surjective ⇑(AlgEquiv.restrictNormalHom ↥E) :=
    AlgEquiv.restrictNormalHom_surjective (F := Q.adicCompletion k) (K₁ := ↥E)
      (E := q.adicCompletion L)
  have hker : (AlgEquiv.restrictNormalHom ↥E).ker = E.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker E
  let Θ : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) ⧸ N ≃*
      (↥E ≃ₐ[Q.adicCompletion k] ↥E) :=
    (QuotientGroup.congr N N' Ψ hmap).trans
      (QuotientGroup.liftEquiv N' hsurj (show N' = (AlgEquiv.restrictNormalHom ↥E).ker from
        hker.symm))
  have hΘmk : ∀ g : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q),
      Θ (QuotientGroup.mk' N g) = AlgEquiv.restrictNormalHom ↥E (Ψ g) :=
    fun g => quotient_congr_trans_liftEquiv_mk' N Ψ N' hmap _ hsurj hker.symm g
  have hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L)
      (NK.GlobalCFT.Place.ofFinite q) ⧸ N) = p := by
    rw [Nat.card_congr Θ.toEquiv,
      ← Nat.card_congr (AlgEquiv.autCongr (AlgHom.equivFieldRange φ)).toEquiv, hF]
  haveI hfinG : Fintype (L ≃ₐ[k] L) := AlgEquiv.fintype k L
  haveI hfinD : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q)) :=
    Fintype.ofFinite _
  haveI hfinQ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L)
      (NK.GlobalCFT.Place.ofFinite q) ⧸ N) :=
    Fintype.ofSurjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hcyc : IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L)
      (NK.GlobalCFT.Place.ofFinite q) ⧸ N) := isCyclic_of_prime_card hcard
  refine ⟨N, hNnorm, hfinQ, hcyc, hcard, ?_⟩
  rintro ⟨bb, hbbN, hsum⟩
  set u₀ : (q.adicCompletion L)ˣ :=
    Additive.toMul (show Additive ((q.adicCompletion L)ˣ) from bb) with hu₀
  have hbb : bb = Additive.ofMul u₀ := by
    rw [hu₀]
    exact (ofMul_toMul (show Additive ((q.adicCompletion L)ˣ) from bb)).symm
  have hfixN : ∀ n : N, NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
      (NK.GlobalCFT.Place.ofFinite q) (n : MulAction.stabilizer (L ≃ₐ[k] L)
        (NK.GlobalCFT.Place.ofFinite q)) u₀ = u₀ := by
    intro n
    have h := hbbN n
    rw [hbb] at h
    change Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
      (NK.GlobalCFT.Place.ofFinite q) (n : MulAction.stabilizer (L ≃ₐ[k] L)
        (NK.GlobalCFT.Place.ofFinite q)) u₀) = Additive.ofMul u₀ at h
    exact Additive.ofMul.injective h
  have hfixN' : ∀ g : (q.adicCompletion L ≃ₐ[Q.adicCompletion k] q.adicCompletion L),
      g ∈ N' → g (u₀ : q.adicCompletion L) = (u₀ : q.adicCompletion L) := by
    intro g hg
    have hn : Ψ.symm g ∈ N := by
      have hmem' : Ψ (Ψ.symm g) ∈ N' := by
        rw [MulEquiv.apply_symm_apply]
        exact hg
      exact hmem'
    have h1 := hfixN ⟨Ψ.symm g, hn⟩
    have hc : (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
        (NK.GlobalCFT.Place.ofFinite q) (Ψ.symm g) u₀ : q.adicCompletion L)
        = (Ψ (Ψ.symm g)) (u₀ : q.adicCompletion L) := by
      rw [NK.HassePrinciple.coe_localUnitsEquiv, hact (Ψ.symm g)]
      rfl
    have h2 : (Ψ (Ψ.symm g)) (u₀ : q.adicCompletion L) = (u₀ : q.adicCompletion L) :=
      hc ▸ congrArg (fun v : (q.adicCompletion L)ˣ => (v : q.adicCompletion L)) h1
    rwa [MulEquiv.apply_symm_apply] at h2
  have hmemE : (u₀ : q.adicCompletion L) ∈ E := by
    have hmem : (u₀ : q.adicCompletion L) ∈ IntermediateField.fixedField E.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      exact hfixN' f hf
    rwa [IsGalois.fixedField_fixingSubgroup (F := Q.adicCompletion k)
      (E := q.adicCompletion L) E] at hmem
  let bu : (↥E)ˣ := Units.mk0 ⟨(u₀ : q.adicCompletion L), hmemE⟩ (by
    intro h; exact Units.ne_zero u₀ (Subtype.ext_iff.mp h))
  have hprodU : (∏ x : MulAction.stabilizer (L ≃ₐ[k] L)
      (NK.GlobalCFT.Place.ofFinite q) ⧸ N,
      NK.HassePrinciple.localUnitsEquiv (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q)
        (Quotient.out x) u₀)
      = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.Place.liesOver_ofFinite hq) a := by
    have h := hsum
    rw [hbb] at h
    have h2 : (∑ x : MulAction.stabilizer (L ≃ₐ[k] L)
        (NK.GlobalCFT.Place.ofFinite q) ⧸ N,
        Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
          (NK.GlobalCFT.Place.ofFinite q) (Quotient.out x) u₀))
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits
            (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite Q)
            (NK.GlobalCFT.Place.liesOver_ofFinite hq) a) := h
    rw [_root_.Work.SSGRoute.fintype_sum_ofMul] at h2
    exact Additive.ofMul.injective h2
  have hlam : NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q)
      (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.Place.liesOver_ofFinite hq)
      = Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toMonoidHom :=
    NK.GlobalCFT.Inclusion.localAlgebraMapUnits_ofFinite_eq q Q hq
  have hii : (∏ x : MulAction.stabilizer (L ≃ₐ[k] L)
      (NK.GlobalCFT.Place.ofFinite q) ⧸ N, (Units.coeHom (q.adicCompletion L))
        (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q)
          (Quotient.out x) u₀))
      = (algebraMap (Q.adicCompletion k) (q.adicCompletion L)) (a : Q.adicCompletion k) := by
    have h := congrArg (fun u : (q.adicCompletion L)ˣ => (u : q.adicCompletion L)) hprodU
    simp only [Units.coe_prod] at h
    simp only [Units.coeHom_apply]
    rw [h, hlam]
    simp only [Units.coe_map,
      RingHom.algebraMap_toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)]
    rfl
  have hptG : ∀ g : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q),
      ((((Θ (QuotientGroup.mk' N g)) bu : ↥E)) : q.adicCompletion L)
        = (Ψ g) (u₀ : q.adicCompletion L) := by
    intro g
    rw [hΘmk g]
    show (((AlgEquiv.restrictNormalHom ↥E (Ψ g)) bu : ↥E) : q.adicCompletion L) = _
    rw [AlgEquiv.restrictNormalHom_apply]
    rfl
  have hiii : (∏ x : MulAction.stabilizer (L ≃ₐ[k] L)
      (NK.GlobalCFT.Place.ofFinite q) ⧸ N, ((((Θ x) bu : ↥E)) : q.adicCompletion L))
      = (∏ x : MulAction.stabilizer (L ≃ₐ[k] L)
        (NK.GlobalCFT.Place.ofFinite q) ⧸ N, (Units.coeHom (q.adicCompletion L))
          (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
            (NK.GlobalCFT.Place.ofFinite q) (Quotient.out x) u₀)) := by
    apply Finset.prod_congr rfl
    intro x _
    have hout : QuotientGroup.mk' N (Quotient.out x) = x :=
      (QuotientGroup.mk'_apply (N := N) (Quotient.out x)).trans (QuotientGroup.out_eq' x)
    have hstep : ((((Θ x) bu : ↥E)) : q.adicCompletion L)
        = ((((Θ (QuotientGroup.mk' N (Quotient.out x))) bu : ↥E)) : q.adicCompletion L) := by
      rw [hout]
    have hwx : (Units.coeHom (q.adicCompletion L))
        (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L) (NK.GlobalCFT.Place.ofFinite q)
          (Quotient.out x) u₀)
        = (Ψ (Quotient.out x)) (u₀ : q.adicCompletion L) := by
      rw [show (Units.coeHom (q.adicCompletion L)) (NK.HassePrinciple.localUnitsEquiv (K := k)
            (L := L) (NK.GlobalCFT.Place.ofFinite q) (Quotient.out x) u₀)
          = (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
              (NK.GlobalCFT.Place.ofFinite q) (Quotient.out x) u₀ : q.adicCompletion L) from rfl,
        NK.HassePrinciple.coe_localUnitsEquiv, hact (Quotient.out x)]
      rfl
    rw [hstep, hptG (Quotient.out x), hwx]
  have hgal : (∏ x : MulAction.stabilizer (L ≃ₐ[k] L)
      (NK.GlobalCFT.Place.ofFinite q) ⧸ N, ((((Θ x) bu : ↥E)) : q.adicCompletion L))
      = (∏ σ : (↥E ≃ₐ[Q.adicCompletion k] ↥E), (((σ bu : ↥E)) : q.adicCompletion L)) := by
    change (∏ x : MulAction.stabilizer (L ≃ₐ[k] L)
        (NK.GlobalCFT.Place.ofFinite q) ⧸ N,
      ((((Θ.toEquiv x) bu : ↥E)) : q.adicCompletion L))
      = (∏ σ : (↥E ≃ₐ[Q.adicCompletion k] ↥E), (((σ bu : ↥E)) : q.adicCompletion L))
    rw [Equiv.prod_comp Θ.toEquiv (fun σ : (↥E ≃ₐ[Q.adicCompletion k] ↥E) =>
      (((σ bu : ↥E)) : q.adicCompletion L))]
  have hnorm : (algebraMap (Q.adicCompletion k) (q.adicCompletion L))
      (Algebra.norm (Q.adicCompletion k) (bu : ↥E))
      = (∏ σ : (↥E ≃ₐ[Q.adicCompletion k] ↥E), (((σ bu : ↥E)) : q.adicCompletion L)) := by
    rw [IsScalarTower.algebraMap_apply (Q.adicCompletion k) ↥E (q.adicCompletion L)
      (Algebra.norm (Q.adicCompletion k) (bu : ↥E))]
    rw [Algebra.norm_eq_prod_automorphisms]
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro σ _
    rfl
  have hkey : (algebraMap (Q.adicCompletion k) (q.adicCompletion L))
      (Algebra.norm (Q.adicCompletion k) (bu : ↥E))
      = (algebraMap (Q.adicCompletion k) (q.adicCompletion L)) (a : Q.adicCompletion k) := by
    rw [hnorm, ← hgal, hiii, hii]
  have hinj : Function.Injective (algebraMap (Q.adicCompletion k) (q.adicCompletion L)) := by
    rw [Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra_algebraMap]
    exact Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective Q q hq
  have hnorm_eq : Algebra.norm (Q.adicCompletion k) (bu : ↥E) = (a : Q.adicCompletion k) :=
    hinj hkey
  have hmem : a ∈ NK.LocalReciprocity.normGroup (Q.adicCompletion k) ↥E := by
    rw [NK.LocalReciprocity.mem_normGroup_iff]
    exact ⟨bu, hnorm_eq⟩
  have hmemF : a ∈ NK.LocalReciprocity.normGroup (Q.adicCompletion k) F := by
    rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv (AlgHom.equivFieldRange φ)]
    exact hmem
  exact ha hmemF

end

end Work.SSGRoute
