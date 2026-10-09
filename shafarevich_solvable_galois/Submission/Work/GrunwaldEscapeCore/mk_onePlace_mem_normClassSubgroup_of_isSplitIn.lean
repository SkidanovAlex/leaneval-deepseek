import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.OrthL2KImports
import Submission.Work.SSGRoute.ZSplit.BaseChange
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GrunwaldEscapeCore

theorem mk_onePlace_mem_normClassSubgroup_of_isSplitIn (p : ℕ) [Fact p.Prime]
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥K)
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N]
    (N' : IntermediateField ↥K Ω) [FiniteDimensional ↥K N'] [IsGalois ↥K N'] [NumberField ↥N']
    (hNN' : (N' : Set Ω) = (N : Set Ω))
    (hsplit : SSGRoute.IsSplitIn k N A) (a : (↥K)ˣ) :
    NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a)) ∈
      NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N' := by
  classical
  -- (1) `N'` is the copy of `N` over `↥K`, so `N'.restrictScalars k = N` as intermediate fields
  have hN'_eq : N'.restrictScalars k = N :=
    SetLike.ext' (by rw [IntermediateField.coe_restrictScalars, hNN'])
  -- (2) `A` splits completely in the `↥K`-extension `N'`
  have hsplitK : SSGRoute.IsSplitIn ↥K N' A :=
    ((Work.SSGRoute.isSplitIn_baseChange k Ω K N' A).mp (by rw [hN'_eq]; exact hsplit)).1
  -- (3) `A` restricts to a finite place of `↥K`
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    rw [h𝔭]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔭
  -- (4) hence the local norm subgroup of `N'/↥K` at `𝔭` is everything
  have htop : NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥N')
      (NK.GlobalCFT.Place.ofFinite 𝔭) = ⊤ :=
    Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_isSplitIn K N' A hAK 𝔭 h𝔭 hsplitK
  -- (5) in particular the local image of `a` at `𝔭` is a local norm
  have hmem : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥N')
        (NK.GlobalCFT.Place.ofFinite 𝔭) := by
    rw [htop]
    exact Subgroup.mem_top _
  -- (6) hence the one-place idèle is an idèle norm
  have hnorm : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a) ∈
      NK.GlobalCFT.Idele.normImage ↥K ↥N' :=
    (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := ↥K) (L := ↥N')
      (NK.GlobalCFT.Place.ofFinite 𝔭) _).mpr hmem
  -- (7) so its class lies in the norm class subgroup
  exact Subgroup.mem_map.mpr ⟨_, hnorm, rfl⟩

end Work.GrunwaldEscapeCore
