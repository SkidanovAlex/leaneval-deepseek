import Mathlib
import Submission.NK.Chebotarev.CompletionOfCompositum
import Submission.NK.Chebotarev.Basic
import Submission.NK.LocalReciprocity.index_normGroup_eq_finrank
import Submission.NK.NUV2.ChebAux.isCyclic_gal_of_compositum
import Submission.NeukirchUchida.Local.LocalGalois
import Submission.NeukirchUchida.Local.Restriction
import Submission.Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
import Submission.NK.Summary.NUV2.Tame.nonempty_algEquiv_of_inertiaDeg_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open NumberField IsDedekindDomain

noncomputable section

namespace NK.KC

/-- The ℚ-adjoin form of `hgen`, which is what `NK.Chebotarev.CompletionOfCompositum` wants. -/
theorem adjoin_rat_eq_top_of_adjoin_eq_top
    {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K L] [Algebra K M] [Algebra K E]
    [Algebra L E] [Algebra M E] [IsScalarTower K L E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤) :
    IntermediateField.adjoin ℚ (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤ := by
  set S : Set E := Set.range (algebraMap L E) ∪ Set.range (algebraMap M E) with hS
  have hsub : (Algebra.adjoin K S : Set E) ⊆ (IntermediateField.adjoin ℚ S : Set E) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact IntermediateField.subset_adjoin ℚ S hy
    | algebraMap r =>
        rw [IsScalarTower.algebraMap_apply K L E r]
        exact IntermediateField.subset_adjoin ℚ S (Set.mem_union_left _ ⟨_, rfl⟩)
    | add y z hy hz ihy ihz => exact (IntermediateField.adjoin ℚ S).add_mem ihy ihz
    | mul y z hy hz ihy ihz => exact (IntermediateField.adjoin ℚ S).mul_mem ihy ihz
  refine top_le_iff.mp ?_
  intro x _
  have hx : x ∈ Algebra.adjoin K S := by rw [hS, hgen]; trivial
  exact hsub hx

/-- **The local ramification index at `w | Q` is the ramification index of `Q` in `M`.** -/
theorem ramificationIdx_eq_ramificationIdxIn {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hw : w.asIdeal.LiesOver Q.asIdeal) :
    w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) =
      Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers M) := by
  letI : MulSemiringAction Gal(M/K) (𝓞 M) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K M (𝓞 M)
  haveI hGal : IsGaloisGroup Gal(M/K) (𝓞 K) (𝓞 M) :=
    IsGaloisGroup.of_isFractionRing Gal(M/K) (𝓞 K) (𝓞 M) K M
  exact (Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 M)
    Q.asIdeal w.asIdeal (Gal(M/K))).symm

/-- **The Galois package for the local extension `E_q / K_Q`.** -/
theorem localGaloisPackage_mine
    {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K L] [Algebra K M] [Algebra K E]
    [Algebra L E] [Algebra M E] [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hw : w.asIdeal.LiesOver Q.asIdeal)
    (hunr : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers M) = 1)
    (hloc : ∀ (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
              (hr : r.asIdeal.LiesOver Q.asIdeal),
      Module.finrank (Q.adicCompletion K) (r.adicCompletion L) ∣
        Module.finrank (Q.adicCompletion K) (w.adicCompletion M))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hq : q.asIdeal.LiesOver w.asIdeal)
    (hQ : q.asIdeal.LiesOver Q.asIdeal) :
    (∀ a b : q.adicCompletion E ≃ₐ[Q.adicCompletion K] q.adicCompletion E, a * b = b * a) ∧
    (∀ a b : q.adicCompletion E ≃ₐ[w.adicCompletion M] q.adicCompletion E, a * b = b * a) ∧
    (∀ σ : q.adicCompletion E ≃ₐ[Q.adicCompletion K] q.adicCompletion E,
      orderOf σ ∣ Module.finrank (Q.adicCompletion K) (w.adicCompletion M)) := by
  classical
  -- the prime of `L` below `q`
  let r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) := q.under _
  have hrq : q.asIdeal.LiesOver r.asIdeal := Ideal.LiesOver.mk rfl
  have hrQ : r.asIdeal.LiesOver Q.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    show Q.asIdeal = Ideal.under (NumberField.RingOfIntegers K) (q.under _).asIdeal
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    exact hQ.over
  -- abbreviations
  haveI hfdC : FiniteDimensional (Q.adicCompletion K) (r.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q r hrQ
  haveI hgalC : IsGalois (Q.adicCompletion K) (r.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q r hrQ
  haveI hnormC : Normal (Q.adicCompletion K) (r.adicCompletion L) := hgalC.to_normal
  haveI hfdF' : FiniteDimensional (Q.adicCompletion K) (w.adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q w hw
  haveI hgalF' : IsGalois (Q.adicCompletion K) (w.adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q w hw
  haveI hnormF' : Normal (Q.adicCompletion K) (w.adicCompletion M) := hgalF'.to_normal
  haveI hfdE' : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hQ
  haveI hgalE' : IsGalois (Q.adicCompletion K) (q.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hQ
  haveI hnormE' : Normal (Q.adicCompletion K) (q.adicCompletion E) := hgalE'.to_normal
  -- the two scalar towers over `K_Q`
  have hSTC : IsScalarTower (Q.adicCompletion K) (r.adicCompletion L) (q.adicCompletion E) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply,
        Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp Q r q hrQ hrq hQ])
  have hSTF' : IsScalarTower (Q.adicCompletion K) (w.adicCompletion M) (q.adicCompletion E) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply,
        Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp Q w q hw hq hQ])
  haveI := hSTC
  haveI := hSTF'
  -- the compositum `E_q = L_r · M_w`, in adjoin form
  have hrangeC : Set.range (algebraMap (r.adicCompletion L) (q.adicCompletion E)) =
      Set.range (Commons.RingTheory.Henselian.adicCompletionMap r q hrq) :=
    congrArg (fun g : r.adicCompletion L →+* q.adicCompletion E =>
      Set.range (g : r.adicCompletion L → q.adicCompletion E))
      (RingHom.algebraMap_toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap r q hrq))
  have hrangeF' : Set.range (algebraMap (w.adicCompletion M) (q.adicCompletion E)) =
      Set.range (Commons.RingTheory.Henselian.adicCompletionMap w q hq) :=
    congrArg (fun g : w.adicCompletion M →+* q.adicCompletion E =>
      Set.range (g : w.adicCompletion M → q.adicCompletion E))
      (RingHom.algebraMap_toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap w q hq))
  have hclosure : Subfield.closure
      (Set.range (algebraMap (r.adicCompletion L) (q.adicCompletion E)) ∪
        Set.range (algebraMap (w.adicCompletion M) (q.adicCompletion E))) = ⊤ := by
    have h := NK.Chebotarev.CompletionOfCompositum L M E
      (adjoin_rat_eq_top_of_adjoin_eq_top hgen) q r hrq w hq
    rwa [← hrangeC, ← hrangeF'] at h
  -- the product of the two restriction maps
  let Ψ : (q.adicCompletion E ≃ₐ[Q.adicCompletion K] q.adicCompletion E) →*
      (r.adicCompletion L ≃ₐ[Q.adicCompletion K] r.adicCompletion L) ×
        (w.adicCompletion M ≃ₐ[Q.adicCompletion K] w.adicCompletion M) :=
    (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K) (K₁ := q.adicCompletion E)
        (r.adicCompletion L)).prod
      (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K) (K₁ := q.adicCompletion E)
        (w.adicCompletion M))
  have hinj : Function.Injective Ψ := by
    intro σ τ h
    have hC : σ.restrictNormal (r.adicCompletion L) = τ.restrictNormal (r.adicCompletion L) :=
      congrArg Prod.fst h
    have hF' : σ.restrictNormal (w.adicCompletion M) = τ.restrictNormal (w.adicCompletion M) :=
      congrArg Prod.snd h
    have hle : Subfield.closure
        (Set.range (algebraMap (r.adicCompletion L) (q.adicCompletion E)) ∪
          Set.range (algebraMap (w.adicCompletion M) (q.adicCompletion E))) ≤
        RingHom.eqLocusField (σ : q.adicCompletion E →+* q.adicCompletion E)
          (τ : q.adicCompletion E →+* q.adicCompletion E) := by
      refine Subfield.closure_le.mpr ?_
      rintro y (hy | hy)
      · obtain ⟨c, rfl⟩ := hy
        show (σ : q.adicCompletion E →+* q.adicCompletion E)
            (algebraMap (r.adicCompletion L) (q.adicCompletion E) c) =
          (τ : q.adicCompletion E →+* q.adicCompletion E)
            (algebraMap (r.adicCompletion L) (q.adicCompletion E) c)
        have h1 := AlgEquiv.restrictNormal_commutes (χ := σ) (r.adicCompletion L) c
        have h2 := AlgEquiv.restrictNormal_commutes (χ := τ) (r.adicCompletion L) c
        rw [hC] at h1
        exact h1.symm.trans h2
      · obtain ⟨m, rfl⟩ := hy
        show (σ : q.adicCompletion E →+* q.adicCompletion E)
            (algebraMap (w.adicCompletion M) (q.adicCompletion E) m) =
          (τ : q.adicCompletion E →+* q.adicCompletion E)
            (algebraMap (w.adicCompletion M) (q.adicCompletion E) m)
        have h1 := AlgEquiv.restrictNormal_commutes (χ := σ) (w.adicCompletion M) m
        have h2 := AlgEquiv.restrictNormal_commutes (χ := τ) (w.adicCompletion M) m
        rw [hF'] at h1
        exact h1.symm.trans h2
    refine AlgEquiv.ext (fun x => ?_)
    exact hle (by rw [hclosure]; trivial)

  -- the order bound
  have hcardC : Nat.card (r.adicCompletion L ≃ₐ[Q.adicCompletion K] r.adicCompletion L) =
      Module.finrank (Q.adicCompletion K) (r.adicCompletion L) :=
    IsGalois.card_aut_eq_finrank _ _
  have hcardF' : Nat.card (w.adicCompletion M ≃ₐ[Q.adicCompletion K] w.adicCompletion M) =
      Module.finrank (Q.adicCompletion K) (w.adicCompletion M) :=
    IsGalois.card_aut_eq_finrank _ _
  have hloc' : Module.finrank (Q.adicCompletion K) (r.adicCompletion L) ∣
      Module.finrank (Q.adicCompletion K) (w.adicCompletion M) := hloc r hrQ
  have hexp : ∀ σ : q.adicCompletion E ≃ₐ[Q.adicCompletion K] q.adicCompletion E,
      orderOf σ ∣ Module.finrank (Q.adicCompletion K) (w.adicCompletion M) := by
    intro σ
    have h1 : orderOf (Ψ σ).1 ∣ Module.finrank (Q.adicCompletion K) (w.adicCompletion M) :=
      dvd_trans (orderOf_dvd_natCard _) (by rw [hcardC]; exact hloc')
    have h2 : orderOf (Ψ σ).2 ∣ Module.finrank (Q.adicCompletion K) (w.adicCompletion M) :=
      dvd_trans (orderOf_dvd_natCard _) (by rw [hcardF'])
    have h3 : orderOf (Ψ σ) ∣ Nat.lcm (orderOf (Ψ σ).1) (orderOf (Ψ σ).2) := by
      rw [orderOf_dvd_iff_pow_eq_one]
      refine Prod.ext ?_ ?_
      · simpa using orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_left _ _)
      · simpa using orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_right _ _)
    have h4 : Nat.lcm (orderOf (Ψ σ).1) (orderOf (Ψ σ).2) ∣
        Module.finrank (Q.adicCompletion K) (w.adicCompletion M) := Nat.lcm_dvd h1 h2
    have h5 : orderOf (Ψ σ) ∣ Module.finrank (Q.adicCompletion K) (w.adicCompletion M) :=
      dvd_trans h3 h4
    rwa [orderOf_injective Ψ hinj σ] at h5
  -- cyclicity of the two factors
  have hunr' : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
    rw [ramificationIdx_eq_ramificationIdxIn Q w hw, hunr]
  have hcycF' : IsCyclic (w.adicCompletion M ≃ₐ[Q.adicCompletion K] w.adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
      Q w hw hunr'
  have hcycC : IsCyclic (r.adicCompletion L ≃ₐ[Q.adicCompletion K] r.adicCompletion L) := by
    haveI hDcyc : IsCyclic
        (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) r) :=
      isCyclic_of_injective
        (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) r).subtype
        (Subgroup.subtype_injective _)
    exact isCyclic_of_injective
      (MulEquiv.toMonoidHom
        (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois Q r hrQ).symm)
      (MulEquiv.injective _)
  have hcommC : ∀ a b : r.adicCompletion L ≃ₐ[Q.adicCompletion K] r.adicCompletion L,
      a * b = b * a := NK.Summary.NUV2.Tame.mul_comm_of_isCyclic hcycC
  have hcommF' : ∀ a b : w.adicCompletion M ≃ₐ[Q.adicCompletion K] w.adicCompletion M,
      a * b = b * a := NK.Summary.NUV2.Tame.mul_comm_of_isCyclic hcycF'
  refine ⟨?_, ?_, hexp⟩
  · intro a b
    refine hinj ?_
    rw [map_mul, map_mul]
    exact Prod.ext (hcommC _ _) (hcommF' _ _)
  · -- `Gal(E_q/M_w)` is commutative: it is the decomposition group of `q` in `Gal(E/M)`,
    -- and `Gal(E/M)` is cyclic by `isCyclic_gal_of_compositum`.
    haveI hgalME : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
    haveI hfdME : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite K M E
    haveI hcycME : IsCyclic (E ≃ₐ[M] E) :=
      NK.NUV2.ChebAux.isCyclic_gal_of_compositum (K := K) (L := L) (M := M) (E := E) hgen hcycL
    haveI hcycDq : IsCyclic (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
        (K := M) (L := E) q) :=
      isCyclic_of_injective (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
          (K := M) (L := E) q).subtype (Subgroup.subtype_injective _)
    have hcyc : IsCyclic (q.adicCompletion E ≃ₐ[w.adicCompletion M] q.adicCompletion E) :=
      isCyclic_of_injective
        (MulEquiv.toMonoidHom
          (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois w q hq).symm)
        (MulEquiv.injective _)
    exact NK.Summary.NUV2.Tame.mul_comm_of_isCyclic hcyc

end NK.KC
