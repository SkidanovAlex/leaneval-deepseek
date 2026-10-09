import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.grunwald_kummer_idx
import Submission.Work.SSGRoute.grunwald_local_setup
import Submission.Work.SSGRoute.grunwald_local_realization
import Submission.Work.SSGRoute.grunwald_setup
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
import Submission.NK.UchidaKummer.Approximation.isWeakApproximation
import Submission.NK.UchidaKummer.Approximation.isOpenEllPowSubgroup
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HRec

open Work.SSGRoute

open scoped Pointwise

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- Grünwald's density result over a number field, `p` odd, in `Hom`-form: for a finite Galois
extension `K/k` of number fields with a primitive `p`-th root of unity in `K` (`p` odd), every
*continuous* additive local datum on the decomposition groups (intersected with `G_K`) of places of a
finite set `T` (one place per prime of `K`) is the restriction of a continuous additive character of
`G_K`.  Via Kummer (`μ_p ⊆ K` makes `μ_p ≅ 𝔽_p` a trivial `G_K`-module, so `H¹(G_K, μ_p) =
Hom(G_K, 𝔽_p)` and `H¹(K_P, μ_p) = Hom(D_P ∩ G_K, 𝔽_p)`) this is the surjectivity of the
localisation `Kˣ/(Kˣ)^p → ∏_{P ∈ T} K_Pˣ/(K_Pˣ)^p`.  For odd `p` there is no Grünwald–Wang
exception (the exceptional case occurs only for `p = 2`).

Continuity of the local data is part of the hypothesis (`hfcont`: an *open subgroup* on which the
datum vanishes, so that `ker (f P)` is open), since the conclusion asks for a locally constant `z`
and additivity alone does not force openness. -/
theorem grunwald_surjective_odd_over_same (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ P ∈ T, SSGRoute.IsFinPlace k P)
    (hTinj : ∀ P Q : {P // P ∈ T},
      (P : ValuationSubring Ω).comap (algebraMap ↥K Ω) =
        (Q : ValuationSubring Ω).comap (algebraMap ↥K Ω) → P = Q)
    (f : ∀ P : {P // P ∈ T},
      ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup) → ZMod p)
    (hf : ∀ P : {P // P ∈ T},
      ∀ a b : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup),
      f P (a * b) = f P a + f P b)
    (hfcont : ∀ P : {P // P ∈ T},
      ∃ U : Subgroup ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup),
        IsOpen (U : Set ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)) ∧
        ∀ x ∈ U, f P x = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ P : {P // P ∈ T},
        ∀ δ : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup),
        z (δ : Ω ≃ₐ[k] Ω) = f P δ) := by
  classical
  haveI hNF : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  haveI hSepK : IsSepClosure ↥K Ω := by
    haveI hAlg : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    exact IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- ### the finite primes of `↥K` below the places of `T`
  have hAK : ∀ P : {P // P ∈ T}, (P : ValuationSubring Ω).comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro P htop
    refine hTfin P.1 P.2 ?_
    refine le_antisymm le_top ?_
    intro x _
    rw [ValuationSubring.mem_comap]
    have h1 : algebraMap ↥K Ω (algebraMap k ↥K x) ∈ (P : ValuationSubring Ω) := by
      rw [← ValuationSubring.mem_comap, htop]
      exact trivial
    rwa [← IsScalarTower.algebraMap_apply k ↥K Ω] at h1
  let pp : {P // P ∈ T} → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
    fun P => Submission.NeukirchUchida.primeOf (K₁ := ↥K) (K₁' := Ω) P.1 (hAK P)
  have hpp : ∀ P : {P // P ∈ T},
      (pp P).valuationSubringAtPrime ↥K = P.1.comap (algebraMap ↥K Ω) :=
    fun P => (Submission.NeukirchUchida.primeOf_spec (K₁ := ↥K) (K₁' := Ω) P.1 (hAK P)).symm
  let S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :=
    T.attach.image pp
  have hpp_inj : ∀ P Q : {P // P ∈ T}, pp P = pp Q → P = Q := by
    intro P Q h
    have hc : P.1.comap (algebraMap ↥K Ω) = Q.1.comap (algebraMap ↥K Ω) := by
      rw [← hpp P, ← hpp Q, h]
    exact hTinj P Q hc
  let placeOf : (q : S) → {P // P ∈ T} := fun q => (Finset.mem_image.mp q.2).choose
  have hplaceOf : ∀ q : S, pp (placeOf q) = q.1 :=
    fun q => (Finset.mem_image.mp q.2).choose_spec.2
  have hppq : ∀ q : S, (placeOf q).1.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q.1 :=
    fun q => (hpp (placeOf q)).symm.trans
      (congrArg (fun w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) =>
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K w) (hplaceOf q))
  have hWq : ∀ q : S, (NK.NeukirchUchida.placeCompletionIntegers (placeOf q).1).comap
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion q.1 (placeOf q).1 (hppq q)) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K q.1 :=
    fun q => NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
      q.1 (placeOf q).1 (hppq q)
  -- ### the identification `decomp k P ⊓ G_K ≃* Aut_κ(M)`
  let eQ : (q : S) → ↥(SSGRoute.decomp k (placeOf q).1 ⊓ K.fixingSubgroup) ≃*
      (localClosure (K' := ↥K) (Ω := Ω) q.1 (placeOf q).1 (hppq q) ≃ₐ[q.1.adicCompletion ↥K]
        localClosure (K' := ↥K) (Ω := Ω) q.1 (placeOf q).1 (hppq q)) :=
    fun q => by
      letI := localAlgebra q.1 (placeOf q).1 (hppq q)
      exact (grunwaldSetupDecompEquiv k Ω K (placeOf q).1).trans
        (NK.Mine.adjoinLocalEquiv (K := ↥K) (K' := Ω) q.1 (placeOf q).1 (hppq q)
          (fun z => rfl) (hWq q))
  have hHomeoQ : ∀ q : S, IsHomeomorph (eQ q) := by
    intro q
    letI := localAlgebra q.1 (placeOf q).1 (hppq q)
    exact NK.Mine.isHomeomorph_trans (grunwaldSetupDecompEquiv k Ω K (placeOf q).1)
      (NK.Mine.adjoinLocalEquiv (K := ↥K) (K' := Ω) q.1 (placeOf q).1 (hppq q)
        (fun z => rfl) (hWq q))
      (isHomeomorph_decompEquiv k Ω K (placeOf q).1)
      (NK.Mine.isHomeomorph_adjoinLocalEquiv q.1 (placeOf q).1 (hppq q) (fun z => rfl) (hWq q))
  -- ### the local additive data
  let gQ : ∀ q : S, (localClosure (K' := ↥K) (Ω := Ω) q.1 (placeOf q).1 (hppq q) ≃ₐ[
      q.1.adicCompletion ↥K]
      localClosure (K' := ↥K) (Ω := Ω) q.1 (placeOf q).1 (hppq q)) → ZMod p :=
    fun q σ => f (placeOf q) ((eQ q).symm σ)
  have hgQ_add : ∀ q : S, ∀ σ τ,
      gQ q (σ * τ) = gQ q σ + gQ q τ := by
    intro q σ τ
    show f (placeOf q) ((eQ q).symm (σ * τ)) =
      f (placeOf q) ((eQ q).symm σ) + f (placeOf q) ((eQ q).symm τ)
    rw [map_mul, hf]
  have hgQ_cont : ∀ q : S, ∃ U : Subgroup (localClosure (K' := ↥K) (Ω := Ω) q.1
      (placeOf q).1 (hppq q) ≃ₐ[q.1.adicCompletion ↥K]
      localClosure (K' := ↥K) (Ω := Ω) q.1 (placeOf q).1 (hppq q)),
      IsOpen (U : Set (localClosure (K' := ↥K) (Ω := Ω) q.1 (placeOf q).1 (hppq q) ≃ₐ[
        q.1.adicCompletion ↥K]
        localClosure (K' := ↥K) (Ω := Ω) q.1 (placeOf q).1 (hppq q))) ∧ ∀ x ∈ U, gQ q x = 0 := by
    intro q
    obtain ⟨U, hUopen, hU⟩ := hfcont (placeOf q)
    refine ⟨U.map (eQ q).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_map]
      exact (hHomeoQ q).isOpenMap _ hUopen
    · rintro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      subst hyx
      show f (placeOf q) ((eQ q).symm ((eQ q) y)) = 0
      rw [MulEquiv.symm_apply_apply]
      exact hU y hy
  -- ### local Kummer elements realising the local data
  let ζK : ↥K := ⟨ζ, hζK⟩
  have hζK' : IsPrimitiveRoot ζK p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hζ
  have hlocQ : ∀ q : S, ∃ (c : (q.1.adicCompletion ↥K)ˣ)
      (γ : (localClosure (K' := ↥K) (Ω := Ω) q.1 (placeOf q).1 (hppq q))ˣ)
      (h : γ ^ p = Units.map (algebraMap (q.1.adicCompletion ↥K)
        (localClosure (K' := ↥K) (Ω := Ω) q.1 (placeOf q).1 (hppq q))) c),
      ∀ σ, kummerIdx p (localRootOfUnity (v := q.1) hζK') c γ h σ = gQ q σ := by
    intro q
    letI := localAlgebra q.1 (placeOf q).1 (hppq q)
    haveI := localClosure_isSepClosure q.1 (placeOf q).1 (hppq q)
    exact exists_local_kummer_element (κ := q.1.adicCompletion ↥K)
      (M := localClosure (K' := ↥K) (Ω := Ω) q.1 (placeOf q).1 (hppq q))
      p (localRootOfUnity (v := q.1) hζK') (gQ q) (hgQ_add q) (hgQ_cont q)
  choose cQ γQ hQ hQspec using hlocQ
  -- ### the weak approximation / Chinese remainder step
  obtain ⟨a, ha⟩ := NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
    (K := ↥K) p S (NK.UchidaKummer.Approximation.isWeakApproximation ↥K S)
    (NK.UchidaKummer.Approximation.isOpenEllPowSubgroup ↥K p Fact.out)
    (fun q => QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (q.1.adicCompletion ↥K) p) (cQ q))
  -- ### the global `p`-th root
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  obtain ⟨α₀, hα₀⟩ := exists_pow_eq_of_isAlgClosed (K := Ω) p
    (Fact.out : p.Prime).ne_zero (algebraMap ↥K Ω (a : ↥K))
  have hα₀ne : α₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at hα₀
    exact (map_ne_zero (algebraMap ↥K Ω)).mpr (Units.ne_zero a) hα₀.symm
  let α : Ωˣ := Units.mk0 α₀ hα₀ne
  have hα : α ^ p = Units.map (algebraMap ↥K Ω) a := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0]
    exact hα₀
  -- ### the global additive character
  let z : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ =>
    if h : σ ∈ K.fixingSubgroup then
      kummerIdx p hζK' a α hα ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, h⟩)
    else 0
  have hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h := by
    intro g hg h hh
    have hgh : g * h ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg hh
    simp only [z, dif_pos hg, dif_pos hh, dif_pos hgh]
    rw [show ((IntermediateField.fixingSubgroupEquiv K) ⟨g * h, hgh⟩) =
        ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩) *
        ((IntermediateField.fixingSubgroupEquiv K) ⟨h, hh⟩) from by
      rw [← map_mul]
      rfl]
    exact kummerIdx_mul_apply p hζK' a α hα _ _
  have hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z := by
    haveI hAlg : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
    have hα₀int : IsIntegral k α₀ :=
      isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic α₀)
    haveI hFinA : FiniteDimensional k ↥(IntermediateField.adjoin k ({α₀} : Set Ω)) :=
      IntermediateField.adjoin.finiteDimensional hα₀int
    haveI hFinS : FiniteDimensional k ↥(K ⊔ IntermediateField.adjoin k ({α₀} : Set Ω)) :=
      IntermediateField.finiteDimensional_sup K _
    refine ⟨(K ⊔ (IntermediateField.adjoin k {α₀})).fixingSubgroup, ?_, ?_⟩
    · exact IntermediateField.fixingSubgroup_isOpen _
    · intro g hg u hu huH
      have huK : u ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_le le_sup_left hu
      have hα₀mem : α₀ ∈ K ⊔ IntermediateField.adjoin k ({α₀} : Set Ω) :=
        (le_sup_right : IntermediateField.adjoin k ({α₀} : Set Ω) ≤
          K ⊔ IntermediateField.adjoin k ({α₀} : Set Ω))
          (IntermediateField.subset_adjoin k ({α₀} : Set Ω) (Set.mem_singleton α₀))
      have hα₀fix : u α₀ = α₀ :=
        (IntermediateField.mem_fixingSubgroup_iff _ u).mp hu α₀ hα₀mem
      have hzu : z u = 0 := by
        simp only [z, dif_pos huK]
        refine kummerIdx_eq_zero_of_apply_eq p hζK' a α hα _ ?_
        show ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩) α₀ = α₀
        exact hα₀fix
      rw [hzadd g hg u huH, hzu, add_zero]
  -- ### agreement with the local data
  have hzagreeQ : ∀ q : S, ∀ δ : ↥(SSGRoute.decomp k (placeOf q).1 ⊓ K.fixingSubgroup),
      z (δ : Ω ≃ₐ[k] Ω) = f (placeOf q) δ := by
    intro q δ
    have hσ''mem : (IntermediateField.fixingSubgroupEquiv K) ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩ ∈
        SSGRoute.decomp ↥K (placeOf q).1 :=
      (fixingSubgroupEquiv_mem_decomp k Ω K (placeOf q).1 (δ : Ω ≃ₐ[k] Ω) δ.2.2).mpr δ.2.1
    letI := localAlgebra q.1 (placeOf q).1 (hppq q)
    let σloc := NK.NeukirchUchida.decompositionToAdjoin (K := ↥K) (K' := Ω)
      q.1 (placeOf q).1 (hppq q) (fun z => rfl)
      ⟨(IntermediateField.fixingSubgroupEquiv K) ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩, hσ''mem⟩
    have hσloc : ∀ y : Ω,
        σloc (coInHom q.1 (placeOf q).1 (hppq q) y) =
          coInHom q.1 (placeOf q).1 (hppq q)
            ((IntermediateField.fixingSubgroupEquiv K) ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩ y) := by
      intro y
      exact NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin (K := ↥K) (K' := Ω)
        q.1 (placeOf q).1 (hppq q) (fun z => rfl)
        ⟨(IntermediateField.fixingSubgroupEquiv K) ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩, hσ''mem⟩ y
    have heQcomm : eQ q δ = σloc := rfl
    have hzdef : z (δ : Ω ≃ₐ[k] Ω) = kummerIdx p hζK' a α hα
        ((IntermediateField.fixingSubgroupEquiv K) ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩) := by
      simp only [z]
      split_ifs with hh
      · rfl
      · exact absurd δ.2.2 hh
    let m : (q.1.adicCompletion ↥K)ˣ :=
      Units.map (algebraMap ↥K (q.1.adicCompletion ↥K)).toMonoidHom a
    have hcl : QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (q.1.adicCompletion ↥K) p)
          (cQ q) =
        QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (q.1.adicCompletion ↥K) p) m :=
      (ha q).symm
    have hmem : (cQ q)⁻¹ * m ∈
        NK.UchidaKummer.ellPowSubgroup (q.1.adicCompletion ↥K) p := QuotientGroup.eq.mp hcl
    have hmem' : (cQ q)⁻¹ * m ∈ (powMonoidHom p).range := hmem
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem'
    have hu' : u ^ p = (cQ q)⁻¹ * m := hu
    have hcu : cQ q = m * (u⁻¹) ^ p := by
      rw [inv_pow, hu']
      group
    calc z (δ : Ω ≃ₐ[k] Ω)
        = kummerIdx p hζK' a α hα
            ((IntermediateField.fixingSubgroupEquiv K) ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩) := hzdef
      _ = kummerIdx p (localRootOfUnity (v := q.1) hζK')
            m (localRoot q.1 (placeOf q).1 (hppq q) α)
            (localRoot_pow q.1 (placeOf q).1 (hppq q) hα) σloc :=
          (kummerIdx_local_eq_global q.1 (placeOf q).1 (hppq q) hζK' a α hα _
            σloc hσloc).symm
      _ = kummerIdx p (localRootOfUnity (v := q.1) hζK') (cQ q) (γQ q) (hQ q) σloc :=
          (kummerIdx_eq_of_mul_pow p (localRootOfUnity (v := q.1) hζK') (cQ q) m (u⁻¹) hcu
            (γQ q) (localRoot q.1 (placeOf q).1 (hppq q) α) (hQ q)
            (localRoot_pow q.1 (placeOf q).1 (hppq q) hα) σloc).symm
      _ = gQ q σloc := hQspec q σloc
      _ = f (placeOf q) δ := by
          show f (placeOf q) ((eQ q).symm σloc) = f (placeOf q) δ
          rw [← heQcomm, MulEquiv.symm_apply_apply]
  -- ### assemble
  refine ⟨z, hzadd, hzloc, ?_⟩
  intro P δ
  let q : S := ⟨pp P, Finset.mem_image.mpr ⟨P, Finset.mem_attach T P, rfl⟩⟩
  have hplace : placeOf q = P := hpp_inj (placeOf q) P (by rw [hplaceOf q])
  let F : {P // P ∈ T} → Type _ := fun P =>
    ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)
  have hcoe : ((cast (congrArg F hplace.symm) δ : F (placeOf q)) : Ω ≃ₐ[k] Ω) =
      (δ : Ω ≃ₐ[k] Ω) :=
    cast_apply_cast (F := F) (fun (P : {P // P ∈ T}) (x : F P) => (x : Ω ≃ₐ[k] Ω))
      hplace.symm δ
  have hfval : f (placeOf q) (cast (congrArg F hplace.symm) δ) = f P δ :=
    cast_apply_cast (F := F) (fun (P : {P // P ∈ T}) (x : F P) => f P x) hplace.symm δ
  rw [← hcoe]
  exact (hzagreeQ q (cast (congrArg F hplace.symm) δ)).trans hfval

end Work.HRec
