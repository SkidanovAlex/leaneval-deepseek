import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.GrunwaldEscapeCore.OrthL2KImports
import Submission.Work.SSGRoute.GrunwaldEscapeCore.CommonsValuationImports
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime
import Submission.Work.SSGRoute.step4_y_escape_v2.GesUFacts
import Submission.Work.SSGRoute.ZSplit.BaseChange
import Submission.Work.GrunwaldEscapeCore.onePlace_mem_gesU_of_kummerChar_eq_zero_on_inertia
import Submission.Work.GrunwaldEscapeCore.prod_localFactor_eq_one_of_comm
import Submission.Work.GrunwaldEscapeCore.mk_onePlace_mem_normClassSubgroup_of_isSplitIn
import Submission.Work.SSGRoute.ZDataTwo.OrthTwoAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `g`-sum of the `p = 2` trichotomy orthogonality

`Work.SSGRoute.ZDataTwo.gsum_trichotomy_two`: for a Kummer element `bg` of the locally constant
datum `g` (`hbg`) and a character `χ` of the idèle class group killing the norm class subgroup of
`N'` (`hχW`), the product of the `T'`-local factors of `bg` under `χ` is `1`.

This is the `p = 2` twin of the `hbprod` computation inside the (proved)
`Work.SSGRoute.GrunwaldEscapeCore.orthogonality_L2K`, with the two `p = 2` changes: the archimedean
factors are killed by the positivity input `harch` (the `p = 2` addition, `hginf` in the
application) instead of by "`K` is totally complex", and the norm subgroup used is that of `N'`
(the `↥K`-copy of `N`) instead of a class field `M`.
-/

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute
open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

/-- **The `g`-sum vanishes.** -/
theorem gsum_trichotomy_two
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (N' : IntermediateField ↥K Ω) [FiniteDimensional ↥K N'] [IsGalois ↥K N'] [NumberField ↥N']
    (hNN' : (N' : Set Ω) = (N : Set Ω))
    (χ : NK.GlobalCFT.IdeleClassGroup ↥K →* Multiplicative (ZMod 2))
    (hχU : Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K) ≤ χ.ker)
    (hχW : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' ≤ χ.ker)
    (bg : (↥K)ˣ)
    (hbg : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      g σ = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg
        (Work.SSGRoute.gesGalKOfFixing K σ hσ))
    (harch : ∀ w : NumberField.InfinitePlace ↥K,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) bg ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥N') (Place.ofInfinite w)) :
    (∏ 𝔭 ∈ T', χ (IdeleClassGroup.mk ↥K
        (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) bg)))) = 1 := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hAlgCl : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  let Ψ : Idele ↥K →* Multiplicative (ZMod 2) := χ.comp (IdeleClassGroup.mk ↥K)
  have hprin : ∀ y : (↥K)ˣ, Ψ (Idele.principalIdele ↥K y) = 1 := by
    intro y
    show χ (IdeleClassGroup.mk ↥K (Idele.principalIdele ↥K y)) = 1
    rw [show IdeleClassGroup.mk ↥K (Idele.principalIdele ↥K y) = 1 from by
      rw [← MonoidHom.mem_ker, Work.SSGRoute.ker_mk_eq_principal]
      exact Idele.mem_principalSubgroup.mpr ⟨y, rfl⟩]
    exact map_one χ
  have hnorm : ∀ y : Idele ↥N', Ψ (Idele.normIdeleHom ↥K ↥N' y) = 1 := by
    intro y
    refine hχW ?_
    exact Subgroup.mem_map.mpr ⟨_, Idele.mem_normImage.mpr ⟨y, fun v => rfl⟩, rfl⟩
  have hs : ∀ v : Place ↥K, v ∉ T'.image Place.ofFinite →
      Ψ (NK.HassePrinciple.onePlace v
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v bg)) = 1 := by
    intro v hv
    rcases v with w | 𝔮
    · -- an archimedean place: the local image is a local norm by `harch`
      have hmem : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) bg ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥N')
            (Place.ofInfinite w) := harch w
      have hnormimg : NK.HassePrinciple.onePlace (Place.ofInfinite w)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) bg) ∈
          Idele.normImage ↥K ↥N' :=
        (NK.CFTLib.IdeleHasse.onePlace_ofInfinite_mem_normImage_iff (K := ↥K) (L := ↥N')
          w _).mpr hmem
      obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hnormimg
      rw [show NK.HassePrinciple.onePlace (Place.ofInfinite w)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) bg) =
          Idele.normIdeleHom ↥K ↥N' y from Idele.ext (fun v => hy v)]
      exact hnorm y
    · -- a finite place `𝔮 ∉ T'`
      have h𝔮T : 𝔮 ∉ T' := fun h => hv (Finset.mem_image_of_mem _ h)
      obtain ⟨B, hBcomap⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
        (K := ↥K) (L := Ω) (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮)
      have hBK : SSGRoute.IsFinPlace ↥K B := by
        rw [SSGRoute.IsFinPlace, hBcomap]
        exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔮
      have hBfin : SSGRoute.IsFinPlace k B :=
        (Work.SSGRoute.isFinPlace_baseChange k Ω K B).mp hBK
      -- `2` is a unit at `B`, since the places over `2` lie in the classes of `T`
      have h2val : ¬ B.valuation (2 : Ω) < 1 := by
        intro hlt
        obtain ⟨A, hA, hconj⟩ := hTcov B hBfin (Or.inl hlt)
        obtain ⟨τ, hτ, hτA⟩ := hconj
        obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
        have hB𝔭 : B.comap (algebraMap ↥K Ω) =
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
          rw [← hτA, ← h𝔭A]
          have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ :=
            funext fun _ => rfl
          rw [(Work.SSGRoute.GrunwaldEscapeCore.gesSmulEqOfCoeEq K hcoe A).symm]
          exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
        rw [hBcomap] at hB𝔭
        exact h𝔮T (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
          hB𝔭 ▸ h𝔭T')
      by_cases hsplit : SSGRoute.IsSplitIn k N B
      · have hmem : IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔮)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg)) ∈
            NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' :=
          Work.GrunwaldEscapeCore.mk_onePlace_mem_normClassSubgroup_of_isSplitIn 2 K B hBfin
            𝔮 hBcomap N N' hNN' hsplit bg
        simpa [Ψ] using hχW hmem
      · -- the inertia criterion: `2 ∣ v_𝔮(bg)`, so the term lies in `U'`
        have hnotT : ∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B := by
          intro A hA hconj
          obtain ⟨τ, hτ, hτA⟩ := hconj
          obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
          have hB𝔭 : B.comap (algebraMap ↥K Ω) =
              IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
            rw [← hτA, ← h𝔭A]
            have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ :=
              funext fun _ => rfl
            rw [(Work.SSGRoute.GrunwaldEscapeCore.gesSmulEqOfCoeEq K hcoe A).symm]
            exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
          rw [hBcomap] at hB𝔭
          exact h𝔮T (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
            hB𝔭 ▸ h𝔭T')
        have hb0 : ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia (k := ↥K) B σ →
            Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg σ = 0 := by
          intro σ hσ
          let τu : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm σ
          have hfix : (IntermediateField.fixingSubgroupEquiv K) τu = σ :=
            (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply σ
          have hτI : SSGRoute.IsInertia k B (τu : Ω ≃ₐ[k] Ω) :=
            (Work.SSGRoute.isInertia_baseChange k Ω K B (τu : Ω ≃ₐ[k] Ω) τu.2).mp
              (by rw [hfix]; exact hσ)
          have hg0 : g (τu : Ω ≃ₐ[k] Ω) = 0 := hgram B hBfin hnotT hsplit _ τu.2 hτI
          have hbτ := hbg (τu : Ω ≃ₐ[k] Ω) τu.2
          rw [show Work.SSGRoute.gesGalKOfFixing K (τu : Ω ≃ₐ[k] Ω) τu.2 = σ from by
            rw [Work.SSGRoute.gesGalKOfFixing]
            rw [show (⟨(τu : Ω ≃ₐ[k] Ω), τu.2⟩ : ↥(K.fixingSubgroup)) = τu from rfl, hfix]] at hbτ
          rw [← hbτ, hg0]
        have hmem : IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔮)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg)) ∈
            Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K 2 T' ⊔
              Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (IdeleClassGroup ↥K) :=
          Work.GrunwaldEscapeCore.onePlace_mem_gesU_of_kummerChar_eq_zero_on_inertia 2 (ζ := ζ) hζ
            T' B hBK 𝔮 hBcomap h𝔮T h2val bg hb0
        simpa [Ψ] using hχU hmem
  have hmain :=
    Work.GrunwaldEscapeCore.prod_localFactor_eq_one_of_comm (p := 2) (K := ↥K) (L := ↥N')
      Ψ hprin hnorm bg (T'.image Place.ofFinite) hs
  rwa [Finset.prod_image (f := fun v : Place ↥K => Ψ (NK.HassePrinciple.onePlace v
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v bg)))
      (s := T') (g := Place.ofFinite)
      (fun x _ y _ hxy => Place.ofFinite_inj.mp hxy)] at hmain

end Work.SSGRoute.ZDataTwo
