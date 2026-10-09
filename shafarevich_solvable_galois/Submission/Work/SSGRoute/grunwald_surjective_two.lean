import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.grunwald_kummer_idx
import Submission.Work.SSGRoute.grunwald_setup
import Submission.Work.SSGRoute.grunwald_local_setup
import Submission.Work.SSGRoute.grunwald_local_realization
import Submission.Work.SSGRoute.ringOfIntegers_mem_of_isFinPlace_k
import Submission.Work.SSGRoute.GrunwaldTwoDefs
import Submission.NK.Mine.AdjoinLocalGalois
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
import Submission.NK.UchidaKummer.Approximation.isOpenEllPowSubgroup
import Submission.NK.UchidaKummer.Approximation.isWeakApproximation
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime

namespace Work.SSGRoute

open scoped Pointwise

/-- The group `K_𝔮ˣ/(K_𝔮ˣ)²` of local `2`-power classes at a finite prime `𝔮` of a number
field `F`. -/
noncomputable def localClassType (F : Type*) [Field F] [NumberField F]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : Type _ :=
  (𝔮.adicCompletion F)ˣ ⧸ NK.UchidaKummer.ellPowSubgroup (𝔮.adicCompletion F) 2

set_option maxHeartbeats 4000000 in
theorem grunwald_surjective_two (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ P ∈ T, SSGRoute.IsFinPlace k P)
    (hTdisj : ∀ P ∈ T, ∀ Q ∈ T, SSGRoute.IsConjPlace k P Q → P = Q)
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
  subst hp2
  classical
  haveI hAlgClosed : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hSepKΩ : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  let ζK : ↥K := ⟨ζ, hζK⟩
  have hζK' : IsPrimitiveRoot ζK 2 := by
    have h : IsPrimitiveRoot ((ζK : ↥K) : Ω) 2 := by simpa [ζK] using hζ
    exact IsPrimitiveRoot.of_map_of_injective (f := (algebraMap ↥K Ω)) h
      (algebraMap ↥K Ω).injective
  -- the prime of `K` below each place of `T`
  have hprimeOf : ∀ P : {P // P ∈ T}, ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥K),
      (P.1.comap (algebraMap ↥K Ω)) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    intro P
    have hcomp : (algebraMap ↥K Ω).comp (algebraMap k ↥K) = algebraMap k Ω := by
      ext r; exact IsScalarTower.algebraMap_apply k ↥K Ω r
    have hne : P.1.comap (algebraMap ↥K Ω) ≠ ⊤ := by
      intro htop
      apply hTfin P.1 P.2
      have h1 : P.1.comap (algebraMap k Ω) =
          (P.1.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) := by
        rw [ValuationSubring.comap_comap, hcomp]
      have htopcomap : (⊤ : ValuationSubring ↥K).comap (algebraMap k ↥K) = ⊤ := by
        apply ValuationSubring.ext
        intro x
        simp [ValuationSubring.mem_comap]
      rw [h1, htop, htopcomap]
    exact Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
      (P.1.comap (algebraMap ↥K Ω)) hne (fun x => by
        rw [ValuationSubring.mem_comap,
          ← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥K) ↥K Ω]
        exact ringOfIntegers_mem_of_isFinPlace_k k Ω P.1 (hTfin P.1 P.2) K x)
  choose 𝔭f h𝔭f using hprimeOf
  have hinj : ∀ P Q : {P // P ∈ T}, 𝔭f P = 𝔭f Q → P = Q := by
    intro P Q hPQ
    apply Subtype.ext
    apply hTdisj P.1 P.2 Q.1 Q.2
    have hcomapK : P.1.comap (algebraMap ↥K Ω) = Q.1.comap (algebraMap ↥K Ω) := by
      rw [h𝔭f P, h𝔭f Q, hPQ]
    have hcompk : (algebraMap ↥K Ω).comp (algebraMap k ↥K) = algebraMap k Ω := by
      ext r; exact IsScalarTower.algebraMap_apply k ↥K Ω r
    have hcomapk : P.1.comap (algebraMap k Ω) = Q.1.comap (algebraMap k Ω) := by
      rw [← hcompk, ← ValuationSubring.comap_comap, ← ValuationSubring.comap_comap, hcomapK]
    obtain ⟨σ, hσ⟩ :=
      Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq (F := k) (E := Ω) P.1 Q.1 hcomapk
    exact ⟨σ, hσ⟩
  -- local realisation of `f P`
  have localData : ∀ P : {P // P ∈ T},
      ∃ yloc : localClassType ↥K (𝔭f P),
        ∀ a : (↥K)ˣ, NK.UchidaKummer.localPowClass ↥K 2 (𝔭f P) a = yloc →
          ∀ δ : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup),
            kummerChar (Ω := Ω) ζK hζK' a
              ((IntermediateField.fixingSubgroupEquiv K) ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩) = f P δ := by
    intro P
    letI : Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P))
        (NK.NeukirchUchida.placeCompletion P.1) := localAlgebra (𝔭f P) P.1 (h𝔭f P)
    have hW : (NK.NeukirchUchida.placeCompletionIntegers P.1).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion (𝔭f P) P.1 (h𝔭f P)) =
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K (𝔭f P) :=
      NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
        (𝔭f P) P.1 (h𝔭f P)
    have halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P),
        algebraMap _ (NK.NeukirchUchida.placeCompletion P.1) z =
          NK.NeukirchUchida.adicCompletionToPlaceCompletion (𝔭f P) P.1 (h𝔭f P) z := fun z => rfl
    let e : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup) ≃*
        (localClosure (K' := ↥K) (Ω := Ω) (𝔭f P) P.1 (h𝔭f P) ≃ₐ[
          IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P)]
          localClosure (K' := ↥K) (Ω := Ω) (𝔭f P) P.1 (h𝔭f P)) :=
      (grunwaldSetupDecompEquiv k Ω K P.1).trans
        (NK.Mine.adjoinLocalEquiv (𝔭f P) P.1 (h𝔭f P) halg hW)
    have h1 : IsHomeomorph (grunwaldSetupDecompEquiv k Ω K P.1 : _ → _) :=
      isHomeomorph_decompEquiv k Ω K P.1
    have h2 : IsHomeomorph (NK.Mine.adjoinLocalEquiv (𝔭f P) P.1 (h𝔭f P) halg hW : _ → _) :=
      NK.Mine.isHomeomorph_adjoinLocalEquiv (𝔭f P) P.1 (h𝔭f P) halg hW
    let g : (localClosure (K' := ↥K) (Ω := Ω) (𝔭f P) P.1 (h𝔭f P) ≃ₐ[
          IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P)]
          localClosure (K' := ↥K) (Ω := Ω) (𝔭f P) P.1 (h𝔭f P)) → ZMod 2 :=
      fun σloc => f P (e.symm σloc)
    have hg : ∀ σ τ, g (σ * τ) = g σ + g τ := by
      intro σ τ
      have h1' : e.symm (σ * τ) = e.symm σ * e.symm τ := map_mul e.symm σ τ
      show f P (e.symm (σ * τ)) = f P (e.symm σ) + f P (e.symm τ)
      rw [h1']
      exact hf P (e.symm σ) (e.symm τ)
    have hgc : ∃ U : Subgroup (localClosure (K' := ↥K) (Ω := Ω) (𝔭f P) P.1 (h𝔭f P) ≃ₐ[
          IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P)]
          localClosure (K' := ↥K) (Ω := Ω) (𝔭f P) P.1 (h𝔭f P)),
        IsOpen (SetLike.coe U) ∧ ∀ x ∈ U, g x = 0 := by
      obtain ⟨U, hUopen, hU⟩ := hfcont P
      refine ⟨(U.map (grunwaldSetupDecompEquiv k Ω K P.1).toMonoidHom).map
        (NK.Mine.adjoinLocalEquiv (𝔭f P) P.1 (h𝔭f P) halg hW).toMonoidHom, ?_, ?_⟩
      · exact h2.isOpenMap _ (h1.isOpenMap (SetLike.coe U) hUopen)
      · intro x hx
        obtain ⟨u, _hu, rfl⟩ := hx
        obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp _hu
        show f P (e.symm ((NK.Mine.adjoinLocalEquiv (𝔭f P) P.1 (h𝔭f P) halg hW)
          ((grunwaldSetupDecompEquiv k Ω K P.1) u'))) = 0
        rw [show (NK.Mine.adjoinLocalEquiv (𝔭f P) P.1 (h𝔭f P) halg hW)
              ((grunwaldSetupDecompEquiv k Ω K P.1) u') = e u' from rfl, MulEquiv.symm_apply_apply]
        exact hU u' hu'
    haveI hsepM : IsSepClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P))
        (localClosure (K' := ↥K) (Ω := Ω) (𝔭f P) P.1 (h𝔭f P)) :=
      localClosure_isSepClosure (𝔭f P) P.1 (h𝔭f P)
    obtain ⟨c, γ, hγ, hc⟩ := exists_local_kummer_element
      (κ := IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P))
      (M := localClosure (K' := ↥K) (Ω := Ω) (𝔭f P) P.1 (h𝔭f P)) 2
      (localRootOfUnity (v := 𝔭f P) hζK') g hg hgc
    refine ⟨QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P)) 2) c, fun a ha δ => ?_⟩
    set σ : Ω ≃ₐ[↥K] Ω := (IntermediateField.fixingSubgroupEquiv K)
      ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩ with hσdef
    have hσ' : σ ∈ NK.Mine.decompositionGroupOf ↥K Ω P.1 := (grunwaldSetupDecompEquiv k Ω K P.1 δ).2
    set σloc := NK.Mine.adjoinLocalEquiv (𝔭f P) P.1 (h𝔭f P) halg hW
      (⟨σ, hσ'⟩ : NK.Mine.decompositionGroupOf ↥K Ω P.1) with hσlocdef
    have hcompat : ∀ y : Ω,
        σloc (coInHom (𝔭f P) P.1 (h𝔭f P) y) = coInHom (𝔭f P) P.1 (h𝔭f P) (σ y) := by
      intro y
      rw [hσlocdef, NK.Mine.adjoinLocalEquiv_apply]
      exact NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin (𝔭f P) P.1 (h𝔭f P) halg
        (⟨σ, hσ'⟩ : NK.Mine.decompositionGroupOf ↥K Ω P.1) y
    have heσ : e δ = σloc := by
      have hσeq : ((grunwaldSetupDecompEquiv k Ω K P.1) δ : Ω ≃ₐ[↥K] Ω) = σ := by
        rw [hσdef]
        rfl
      have hA : ((grunwaldSetupDecompEquiv k Ω K P.1) δ : NK.Mine.decompositionGroupOf ↥K Ω P.1)
          = (⟨σ, hσ'⟩ : NK.Mine.decompositionGroupOf ↥K Ω P.1) := Subtype.ext hσeq
      exact (congrArg (NK.Mine.adjoinLocalEquiv (𝔭f P) P.1 (h𝔭f P) halg hW) hA).trans
        hσlocdef.symm
    have hbr := kummerIdx_local_eq_global (𝔭f P) P.1 (h𝔭f P) hζK' a
      (kummerSqrt (Ω := Ω) a) (kummerSqrt_pow (Ω := Ω) a) σ σloc hcompat
    obtain ⟨u, hu⟩ : ∃ u : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P))ˣ,
        c = Units.map (algebraMap ↥K
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P))).toMonoidHom a * u ^ 2 := by
      have hq := ha
      rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply] at hq
      obtain ⟨u, hu⟩ := QuotientGroup.eq.mp hq
      exact ⟨u, by
        have hu' : u ^ 2 = (Units.map (algebraMap ↥K
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P))).toMonoidHom a)⁻¹ * c := hu
        rw [hu']
        group⟩
    have hcl := kummerIdx_eq_of_mul_pow 2 (localRootOfUnity (v := 𝔭f P) hζK') c
      (Units.map (algebraMap ↥K
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P))).toMonoidHom a) u hu
      γ (localRoot (𝔭f P) P.1 (h𝔭f P) (kummerSqrt (Ω := Ω) a))
      hγ (localRoot_pow (𝔭f P) P.1 (h𝔭f P) (kummerSqrt_pow (Ω := Ω) a)) σloc
    have hgv : g σloc = f P δ := by
      have h : e.symm σloc = δ := by rw [← heσ, MulEquiv.symm_apply_apply]
      show f P (e.symm σloc) = f P δ
      rw [h]
    calc kummerChar (Ω := Ω) ζK hζK' a
            ((IntermediateField.fixingSubgroupEquiv K) ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩)
        = kummerIdx 2 hζK' a (kummerSqrt (Ω := Ω) a) (kummerSqrt_pow (Ω := Ω) a) σ := rfl
      _ = kummerIdx 2 (localRootOfUnity (v := 𝔭f P) hζK')
            (Units.map (algebraMap ↥K
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ↥K (𝔭f P))).toMonoidHom a)
            (localRoot (𝔭f P) P.1 (h𝔭f P) (kummerSqrt (Ω := Ω) a))
            (localRoot_pow (𝔭f P) P.1 (h𝔭f P) (kummerSqrt_pow (Ω := Ω) a)) σloc := hbr.symm
      _ = kummerIdx 2 (localRootOfUnity (v := 𝔭f P) hζK') c γ hγ σloc := hcl.symm
      _ = g σloc := hc σloc
      _ = f P δ := hgv
  choose yloc hyloc using localData
  -- the finite set of primes below `T`, and the equivalence with `T`
  let S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :=
    T.attach.image 𝔭f
  let eTS : {P // P ∈ T} ≃ {𝔮 // 𝔮 ∈ S} := Equiv.ofBijective
    (fun P => ⟨𝔭f P, Finset.mem_image.mpr ⟨P, Finset.mem_attach T P, rfl⟩⟩)
    (by
      constructor
      · intro P Q hPQ
        exact hinj P Q (by simpa using congrArg Subtype.val hPQ)
      · rintro ⟨𝔮, h𝔮⟩
        obtain ⟨P, -, hPeq⟩ := Finset.mem_image.mp h𝔮
        exact ⟨P, Subtype.ext hPeq⟩)
  -- transport the local data along `eTS`
  let P' := fun 𝔮 : {𝔮 // 𝔮 ∈ S} => localClassType ↥K 𝔮.1
  let y : ∀ 𝔮 : {𝔮 // 𝔮 ∈ S}, localClassType ↥K 𝔮.1 := Equiv.piCongrLeft P' eTS yloc
  have hy_eTS : ∀ P, y (eTS P) = yloc P := by
    intro P
    change (Equiv.piCongrLeft P' eTS) yloc (eTS P) = yloc P
    rw [← Equiv.piCongrLeft_symm_apply (P := P') (e := eTS)
      ((Equiv.piCongrLeft P' eTS) yloc) P]
    exact congrFun (Equiv.symm_apply_apply (Equiv.piCongrLeft P' eTS) yloc) P
  obtain ⟨b, hb⟩ := (NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
    (K := ↥K) 2 S (NK.UchidaKummer.Approximation.isWeakApproximation ↥K S)
    (NK.UchidaKummer.Approximation.isOpenEllPowSubgroup ↥K 2 (by norm_num))) y
  refine ⟨fun σ => if h : σ ∈ K.fixingSubgroup then
      kummerChar (Ω := Ω) ζK hζK' b
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, h⟩) else 0, ?_, ?_, ?_⟩
  · intro gg hg hh hhh
    have hgh : gg * hh ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg hhh
    simp only [dif_pos hg, dif_pos hhh, dif_pos hgh]
    have key : (⟨gg * hh, hgh⟩ : ↥K.fixingSubgroup) = ⟨gg, hg⟩ * ⟨hh, hhh⟩ := Subtype.ext rfl
    rw [key, map_mul (IntermediateField.fixingSubgroupEquiv K), kummerChar_mul_apply]
  · haveI hfdL : FiniteDimensional k
        ↥(IntermediateField.adjoin k {kummerSqrtVal (K := ↥K) (Ω := Ω) b}) :=
      IntermediateField.adjoin.finiteDimensional (K := k)
        (x := kummerSqrtVal (K := ↥K) (Ω := Ω) b)
        ((Algebra.IsAlgebraic.isIntegral (K := k) (A := Ω)).isIntegral _)
    refine ⟨K.fixingSubgroup ⊓ (IntermediateField.adjoin k
        {kummerSqrtVal (K := ↥K) (Ω := Ω) b}).fixingSubgroup, ?_, ?_⟩
    · exact (IntermediateField.fixingSubgroup_isOpen K).inter
        (IntermediateField.fixingSubgroup_isOpen _)
    · intro gg hg u hu huH
      obtain ⟨huK, huL⟩ := Subgroup.mem_inf.mp hu
      have hgu : gg * u ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg huK
      simp only [dif_pos hg, dif_pos hgu]
      have key : (⟨gg * u, hgu⟩ : ↥K.fixingSubgroup) = ⟨gg, hg⟩ * ⟨u, huK⟩ := Subtype.ext rfl
      rw [key, map_mul (IntermediateField.fixingSubgroupEquiv K), kummerChar_mul_apply]
      have hfix : ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩ : Ω ≃ₐ[↥K] Ω)
            ((kummerSqrt (Ω := Ω) b : Ωˣ) : Ω) = ((kummerSqrt (Ω := Ω) b : Ωˣ) : Ω) := by
        have hmem : kummerSqrtVal (K := ↥K) (Ω := Ω) b ∈ (IntermediateField.adjoin k
            {kummerSqrtVal (K := ↥K) (Ω := Ω) b} : IntermediateField k Ω) :=
          IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
        have hfixu : (u : Ω ≃ₐ[k] Ω) (kummerSqrtVal (K := ↥K) (Ω := Ω) b)
            = kummerSqrtVal (K := ↥K) (Ω := Ω) b :=
          (IntermediateField.mem_fixingSubgroup_iff _ _).mp huL _ hmem
        have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩ : Ω ≃ₐ[↥K] Ω)
            = ⇑(u : Ω ≃ₐ[k] Ω) := by ext x; rfl
        exact (congrFun hcoe ((kummerSqrt (Ω := Ω) b : Ωˣ) : Ω)).trans (by simpa only [kummerSqrt, Units.val_mk0] using hfixu)
      have hzero : kummerChar (Ω := Ω) ζK hζK' b
          ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩) = 0 :=
        kummerIdx_eq_zero_of_apply_eq 2 hζK' b (kummerSqrt (Ω := Ω) b)
          (kummerSqrt_pow (Ω := Ω) b) _ hfix
      rw [hzero, add_zero]
  · intro P δ
    have h1 : NK.UchidaKummer.localPowClass ↥K 2 (𝔭f P) b = yloc P := by
      have h2 : NK.UchidaKummer.localPowClass ↥K 2 (𝔭f P) b = y (eTS P) := hb (eTS P)
      rw [h2, hy_eTS P]
    have hδ : (δ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := δ.2.2
    show (if h : (δ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup then
      kummerChar (Ω := Ω) ζK hζK' b ((IntermediateField.fixingSubgroupEquiv K)
        ⟨(δ : Ω ≃ₐ[k] Ω), h⟩) else 0) = f P δ
    rw [dif_pos hδ]
    exact hyloc P b h1 δ
end Work.SSGRoute
