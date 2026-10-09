import Mathlib
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.InertiaArithImports
import Submission.Work.SSGRoute.mem_localInertia_iff_isInertia
import Submission.Work.SSGRoute.isInertia_of_fixes_rootsOfUnity_gen
import Submission.Work.SSGRoute.isUnit_natCast_iff_not_dvd_resCharAt
import Submission.Work.SSGRoute.charP_residueField_isFinPlace
import Submission.Work.SSGRoute.PT.inertia_wild_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

/-!
# The wild inertia subgroup of a finite place (residue characteristic `≠ p`)

Let `k` be a number field, `Ω = k̄` an algebraic closure, `A` a finite place of `Ω` over `k` at
which the rational prime `p` is a *unit* (equivalently: the residue characteristic `q` of `A`
is different from `p`).  Then the inertia subgroup `I_A ≤ G_k` has a closed normal subgroup
`W` — the *wild inertia* — which is pro-prime-to-`p` and such that every normal finite-index
subgroup of `I_A` containing `W` has cyclic quotient.

The subgroup is the transport, along the homeomorphism `e : D_A ≃* Gal(κ̄/κ)` of the decomposition
group with the absolute Galois group of the completion `κ = k_𝔭` (Neukirch–Uchida local
decomposition), of the wild inertia `V_κ` of the local field: the maximal closed normal
pro-`q` subgroup of `Gal(κ̄/κ)`, which satisfies `V_κ ≤ I_κ` with `I_κ/V_κ` pro-cyclic
(`NK.TameStructureDeep`, unconditional, at every `𝔭`-adic completion).
-/

open scoped Pointwise

namespace Work.SSGRoute.PT



section Helpers

/-- **Pro-`q` implies pro-prime-to-`p`** when `q` is a prime not dividing `p`. -/
theorem isProPrimeToP_of_isProP_of_not_dvd {G : Type*} [Group G] {q p : ℕ} (hq : q.Prime)
    (hndvd : ¬ q ∣ p) (h : NK.LocalTame.IsProP q G) : Work.SSGRoute.IsProPrimeToP p G := by
  intro N hN hfi
  obtain ⟨k, hk⟩ := h N hfi
  rw [hk]
  exact (((hq.coprime_iff_not_dvd).mpr hndvd).pow_left k).symm

/-- The inclusion of a subgroup into a larger one, as a monoid homomorphism. -/
def subgroupInclusion {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) : ↥H →* ↥K :=
  { toFun := fun x => ⟨(x : G), h x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

/-- **`G ⧸ U` is cyclic whenever `H` is pro-cyclic and `φ : G ↠ H` has kernel inside `U`.** -/
theorem isCyclic_quotient_of_isProCyclic_of_surjective {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Surjective φ) (hH : NK.LocalTame.IsProCyclic H)
    {U : Subgroup G} [U.Normal] (hU : U.FiniteIndex) (hker : φ.ker ≤ U) :
    IsCyclic (G ⧸ U) := by
  haveI hN : (U.map φ).Normal := ‹U.Normal›.map φ hφ
  have hfim : (U.map φ).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_map]
    rw [show U ⊔ φ.ker = U from sup_eq_left.mpr hker, MonoidHom.range_eq_top.mpr hφ]
    simpa using (Subgroup.finiteIndex_iff.mp hU)
  have hcyc : IsCyclic (H ⧸ U.map φ) := hH _ hfim
  have hsurj : Function.Surjective ((QuotientGroup.mk' (U.map φ)).comp φ) :=
    (QuotientGroup.mk'_surjective _).comp hφ
  have hker2 : ((QuotientGroup.mk' (U.map φ)).comp φ).ker = U := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro hx
      have h1 : φ x ∈ U.map φ := (QuotientGroup.eq_one_iff (φ x)).mp hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
      have h2 : y⁻¹ * x ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have h4 : y * (y⁻¹ * x) ∈ U := U.mul_mem hy (hker h2)
      rwa [mul_inv_cancel_left] at h4
    · intro hx
      exact (QuotientGroup.eq_one_iff (φ x)).mpr (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hiso : G ⧸ U ≃* H ⧸ U.map φ :=
    (QuotientGroup.quotientMulEquivOfEq hker2).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)
  exact isCyclic_of_surjective hiso.symm hiso.symm.surjective

end Helpers

theorem inertia_wild_exists
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) :
    ∃ W : Subgroup (Ω ≃ₐ[k] Ω),
      W ≤ SSGRoute.inertiaSub k Ω A ∧
      (∀ δ ∈ SSGRoute.inertiaSub k Ω A, ∀ w ∈ W, δ * w * δ⁻¹ ∈ W) ∧
      IsClosed (W : Set (Ω ≃ₐ[k] Ω)) ∧
      Work.SSGRoute.IsProPrimeToP p ↥W ∧
      (∀ (U : Subgroup (Ω ≃ₐ[k] Ω)), W ≤ U → U ≤ SSGRoute.inertiaSub k Ω A →
        (hUn : (U.subgroupOf (SSGRoute.inertiaSub k Ω A)).Normal) →
        (hUf : (U.subgroupOf (SSGRoute.inertiaSub k Ω A)).FiniteIndex) →
        IsCyclic (↥(SSGRoute.inertiaSub k Ω A) ⧸ U.subgroupOf (SSGRoute.inertiaSub k Ω A))) := by
  classical
  haveI hsep : IsSepClosure k Ω := inferInstance
  -- ### the local structure of the completion
  have hcore := NK.TameStructureDeep.Tame.tameRamificationCore_adicCompletion_residueChar
    (K' := locClosure k Ω A hA) (placePrime k Ω A hA)
  have hqprime : (resQ k Ω A hA).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion (placePrime k Ω A hA)
  have hVnormal : (locV k Ω A hA).Normal := NK.LocalTame.wildInertiaSubgroup_normal _
  have hVleI : locV k Ω A hA ≤ locI k Ω A hA := hcore.wildInertia_le_inertia
  have hVpro : NK.LocalTame.IsProP (resQ k Ω A hA) ↥(locV k Ω A hA) :=
    NK.LocalTame.Galois.wildInertiaSubgroup_isProP _
  have hVclosed : IsClosed ((locV k Ω A hA : Set (locGal k Ω A hA))) :=
    NK.TameStructureDeep.Support.wildInertiaSubgroup_isClosed _ hqprime
  have hInorm : (locI k Ω A hA).Normal := NK.LocalAnabelian.inertiaSubgroup_normal _
  have hIprocyclic : NK.LocalTame.IsProCyclic ((locI k Ω A hA : Type) ⧸ (locV k Ω A hA).subgroupOf (locI k Ω A hA)) :=
    (NK.TameStructureDeep.Support.isProCyclic_quotientImage_iff).mp hcore.isProCyclic_tameInertia
  -- ### `q ≠ p`
  have hqne : resQ k Ω A hA ≠ p := by
    intro hqp
    have hpun : IsUnit ((p : ℕ) : ↥A) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hbad
      exact h (by
        have := (ValuationSubring.valuation_lt_one_iff A ((p : ℕ) : ↥A)).mp hbad
        simpa using this)
    have hnotun : ¬ IsUnit ((p : ℕ) : ↥A) := by
      rw [Work.SSGRoute.isUnit_natCast_iff_not_dvd_resCharAt k Ω A hA p]
      have hres : NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A hA) = p := hqp
      rw [hres]
      exact fun hh => hh dvd_rfl
    exact hnotun hpun
  have hndvd : ¬ resQ k Ω A hA ∣ p := by
    intro hdvd
    rcases (Fact.out (p := p.Prime)).eq_one_or_self_of_dvd (resQ k Ω A hA) hdvd with h1 | h1
    · exact hqprime.ne_one h1
    · exact hqne h1
  -- ### the homeomorphic identification of `D_A` with the local Galois group
  let e₀ : ↥(SSGRoute.decomp k A) ≃* locGal k Ω A hA := NK.ResidueFrob.localGaloisEquivAdjoin ⟨A, hA⟩
  have hhomeo : IsHomeomorph (e₀ : ↥(SSGRoute.decomp k A) → locGal k Ω A hA) := by
    letI : Algebra (NK.FrobeniusBridge.localField ⟨A,hA⟩) (NK.NeukirchUchida.placeCompletion A) :=
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (placePrime k Ω A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
    have hW := NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
      (placePrime k Ω A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)
    haveI hSep : IsSepClosure (locField k Ω A hA)
        ↥(NK.NeukirchUchida.adjoinPlaceCompletion (placePrime k Ω A hA) A) :=
      NK.Mine.isSepClosure_adjoinPlaceCompletion (placePrime k Ω A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
    have hMine : IsHomeomorph (NK.Mine.localGaloisEquiv (placePrime k Ω A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl) hW :
        ↥(SSGRoute.decomp k A) → locGal k Ω A hA) :=
      NK.Mine.isHomeomorph_trans _ _
        (NK.Mine.isHomeomorph_adjoinLocalEquiv _ A (Submission.NeukirchUchida.primeOf_spec A hA)
          (fun z => rfl) hW)
        (NK.Mine.isHomeomorph_autCongr _)
    have heq : NK.ResidueFrob.localGaloisEquivAdjoin ⟨A, hA⟩ =
        NK.Mine.localGaloisEquiv (placePrime k Ω A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl) hW := by
      refine MulEquiv.ext fun σ => ?_
      simp only [NK.ResidueFrob.localGaloisEquivAdjoin, NK.ResidueFrob.adjoinLocalIso,
        NK.Mine.localGaloisEquiv, MulEquiv.trans_apply, AlgEquiv.autCongr_apply,
        NK.ResidueFrob.decompositionAdjoinEquiv_apply, NK.Mine.adjoinLocalEquiv_apply]
      rfl
    rw [show e₀ = NK.Mine.localGaloisEquiv (placePrime k Ω A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl) hW from heq]
    exact hMine
  -- ### the inertia matching
  have hunit : ∀ n : ℕ, ¬ resQ k Ω A hA ∣ n → IsUnit (n : ↥A) := fun n hn =>
    (Work.SSGRoute.isUnit_natCast_iff_not_dvd_resCharAt k Ω A hA n).mpr hn
  have hmatch : ∀ σ : ↥(SSGRoute.decomp k A),
      SSGRoute.IsInertia k A (σ : Ω ≃ₐ[k] Ω) ↔ e₀ σ ∈ locI k Ω A hA := by
    intro σ
    rw [show e₀ σ ∈ locI k Ω A hA ↔
        (NK.FrobeniusBridge.localGaloisEquiv ⟨A, hA⟩) σ ∈ locI k Ω A hA from ?_]
    exact Work.SSGRoute.mem_localInertia_iff_isInertia ⟨A, hA⟩ hunit σ
    have hT : NK.LocalTame.TameData (resQ k Ω A hA)
        (NK.LocalStructure.residueCard k (placePrime k Ω A hA))
        (locField k Ω A hA) (locClosure k Ω A hA) :=
      NK.TameData.TameDataInput.toTameData
        (NK.TameStructureDeep.Tame.tameDataInput_adicCompletion_residueChar (placePrime k Ω A hA))
    exact NK.LocalTame.inertiaOfDecomposition_iff_of_localIso hT e₀
      (NK.FrobeniusBridge.localGaloisEquiv ⟨A, hA⟩) σ
  -- ### the witness
  let Wsub : Subgroup ↥(SSGRoute.decomp k A) := (locV k Ω A hA).comap (e₀ : ↥(SSGRoute.decomp k A) →* locGal k Ω A hA)
  let W : Subgroup (Ω ≃ₐ[k] Ω) := Wsub.map (SSGRoute.decomp k A).subtype
  have hmemWsub : ∀ d : ↥(SSGRoute.decomp k A), d ∈ Wsub ↔
      (e₀ : ↥(SSGRoute.decomp k A) →* locGal k Ω A hA) d ∈ locV k Ω A hA := fun d => Iff.rfl
  have hWleJ : W ≤ SSGRoute.inertiaSub k Ω A := by
    intro w hw
    rw [Work.SSGRoute.mem_inertiaSub]
    rw [Subgroup.mem_map] at hw
    obtain ⟨d, hd, hdw⟩ := hw
    rw [← hdw]
    exact (hmatch d).mpr (hVleI hd)
  refine ⟨W, hWleJ, ?_, ?_, ?_, ?_⟩
  · -- normality of `W` in `I_A`
    intro δ hδ w hw
    have hδD : δ ∈ SSGRoute.decomp k A := (Work.SSGRoute.mem_inertiaSub k Ω A δ).mp hδ |>.1
    rw [Subgroup.mem_map] at hw ⊢
    obtain ⟨d, hd, hdw⟩ := hw
    refine ⟨⟨δ, hδD⟩ * d * ⟨δ, hδD⟩⁻¹, (hmemWsub _).mpr ?_, ?_⟩
    · let eH : ↥(SSGRoute.decomp k A) →* locGal k Ω A hA := e₀
      have hconj : eH (⟨δ, hδD⟩ * d * ⟨δ, hδD⟩⁻¹)
          = eH ⟨δ, hδD⟩ * eH d * (eH ⟨δ, hδD⟩)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [hconj]
      exact hVnormal.conj_mem (eH d) ((hmemWsub d).mp hd) (eH ⟨δ, hδD⟩)
    · rw [← hdw]
      rfl
  · -- closedness of `W`
    have hDclosed : IsClosed ((SSGRoute.decomp k A : Set (Ω ≃ₐ[k] Ω))) :=
      Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A
    have hWsub : IsClosed (Wsub : Set ↥(SSGRoute.decomp k A)) :=
      hVclosed.preimage hhomeo.continuous
    have himg : IsClosed ((Subtype.val : ↥(SSGRoute.decomp k A) → Ω ≃ₐ[k] Ω) ''
        (Wsub : Set ↥(SSGRoute.decomp k A))) :=
      (IsClosed.isClosedMap_subtype_val hDclosed) _ hWsub
    have hcoe : (W : Set (Ω ≃ₐ[k] Ω))
        = (Subtype.val : ↥(SSGRoute.decomp k A) → Ω ≃ₐ[k] Ω)
          '' (Wsub : Set ↥(SSGRoute.decomp k A)) := by
      rw [show W = Wsub.map (SSGRoute.decomp k A).subtype from rfl, Subgroup.coe_map]
      rfl
    rw [hcoe]
    exact himg
  · -- `W` is pro-prime-to-`p`
    have hWpro : NK.LocalTame.IsProP (resQ k Ω A hA) ↥W := by
      have heV : ↥W ≃* ↥(locV k Ω A hA) :=
        (Subgroup.equivMapOfInjective Wsub (SSGRoute.decomp k A).subtype
            (fun a b h => Subtype.ext h)).symm.trans
          ((Subgroup.equivMapOfInjective ((locV k Ω A hA).comap
                (e₀ : ↥(SSGRoute.decomp k A) →* locGal k Ω A hA))
              (e₀ : ↥(SSGRoute.decomp k A) →* locGal k Ω A hA) e₀.injective).trans
            (MulEquiv.subgroupCongr
              (Subgroup.map_comap_eq_self_of_surjective e₀.surjective (locV k Ω A hA))))
      exact (NK.LocalTame.isProP_congr heV (resQ k Ω A hA)).mpr hVpro
    exact isProPrimeToP_of_isProP_of_not_dvd hqprime hndvd hWpro
  · -- every normal finite-index subgroup of `I_A` containing `W` has cyclic quotient
    intro U hWU hUJ hUn hUf
    haveI := hUn
    haveI hVI : ((locV k Ω A hA).subgroupOf (locI k Ω A hA)).Normal :=
      Subgroup.Normal.subgroupOf hVnormal (locI k Ω A hA)
    have hJD : SSGRoute.inertiaSub k Ω A ≤ SSGRoute.decomp k A :=
      Work.SSGRoute.inertiaSub_le_decomp k Ω A
    let ρ : ↥(SSGRoute.inertiaSub k Ω A) →* locGal k Ω A hA :=
      (e₀ : ↥(SSGRoute.decomp k A) →* locGal k Ω A hA).comp (subgroupInclusion hJD)
    have hρapply : ∀ x : ↥(SSGRoute.inertiaSub k Ω A), ρ x =
        (e₀ : ↥(SSGRoute.decomp k A) →* locGal k Ω A hA) ⟨(x : Ω ≃ₐ[k] Ω), hJD x.2⟩ :=
      fun _ => rfl
    have hρmem : ∀ x : ↥(SSGRoute.inertiaSub k Ω A), ρ x ∈ locI k Ω A hA := fun x =>
      (hmatch ⟨(x : Ω ≃ₐ[k] Ω), hJD x.2⟩).mp
        ((Work.SSGRoute.mem_inertiaSub k Ω A (x : Ω ≃ₐ[k] Ω)).mpr x.2)
    let ρI : ↥(SSGRoute.inertiaSub k Ω A) →* ↥(locI k Ω A hA) :=
      ρ.codRestrict (locI k Ω A hA) hρmem
    have hρIapply : ∀ x : ↥(SSGRoute.inertiaSub k Ω A),
        ((ρI x : ↥(locI k Ω A hA)) : locGal k Ω A hA) = ρ x := fun _ => rfl
    let ψ : ↥(SSGRoute.inertiaSub k Ω A) →*
        (locI k Ω A hA : Type) ⧸ (locV k Ω A hA).subgroupOf (locI k Ω A hA) :=
      (QuotientGroup.mk' ((locV k Ω A hA).subgroupOf (locI k Ω A hA))).comp ρI
    have hψsurj : Function.Surjective ψ := by
      intro y
      obtain ⟨z, rfl⟩ :=
        QuotientGroup.mk'_surjective ((locV k Ω A hA).subgroupOf (locI k Ω A hA)) y
      have hzmem : ((e₀.symm z : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω)
          ∈ SSGRoute.inertiaSub k Ω A :=
        (hmatch (e₀.symm z)).mpr (by rw [MulEquiv.apply_symm_apply]; exact z.2)
      refine ⟨(⟨((e₀.symm z : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω), hzmem⟩ :
        ↥(SSGRoute.inertiaSub k Ω A)), ?_⟩
      · have hz : ρI (⟨((e₀.symm z : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω), hzmem⟩ :
            ↥(SSGRoute.inertiaSub k Ω A)) = z := by
          apply Subtype.ext
          rw [hρIapply]
          show ρ _ = (z : locGal k Ω A hA)
          rw [hρapply]
          rw [show (⟨((e₀.symm z : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω), _⟩ :
              ↥(SSGRoute.decomp k A)) = e₀.symm z from Subtype.ext rfl]
          exact e₀.apply_symm_apply z
        rw [show ψ (⟨((e₀.symm z : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω), hzmem⟩ :
              ↥(SSGRoute.inertiaSub k Ω A))
            = QuotientGroup.mk' _
              (ρI (⟨((e₀.symm z : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω), hzmem⟩ :
                ↥(SSGRoute.inertiaSub k Ω A))) from rfl, hz]
    have hker : ψ.ker ≤ U.subgroupOf (SSGRoute.inertiaSub k Ω A) := by
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      have h1 : ρI x ∈ (locV k Ω A hA).subgroupOf (locI k Ω A hA) :=
        (QuotientGroup.eq_one_iff (ρI x)).mp hx
      have h2 : ρ x ∈ locV k Ω A hA := by
        rw [← hρIapply x]
        exact Subgroup.mem_subgroupOf.mp h1
      have h3 : (⟨(x : Ω ≃ₐ[k] Ω), hJD x.2⟩ : ↥(SSGRoute.decomp k A)) ∈ Wsub :=
        (hmemWsub _).mpr h2
      have hWx : (x : Ω ≃ₐ[k] Ω) ∈ W := by
        rw [show W = Wsub.map (SSGRoute.decomp k A).subtype from rfl, Subgroup.mem_map]
        exact ⟨_, h3, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact hWU hWx
    exact isCyclic_quotient_of_isProCyclic_of_surjective ψ hψsurj hIprocyclic hUf hker

end Work.SSGRoute.PT
