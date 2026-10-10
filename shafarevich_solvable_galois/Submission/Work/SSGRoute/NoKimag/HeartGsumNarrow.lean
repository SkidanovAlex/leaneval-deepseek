import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.N2v2.heart_chi1_part
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `g`-sum of the escape orthogonality

The product formula for the pair `(χ_{c₁}, bg)` together with the analysis of the places outside
`T'`.  See `NOTE_session_chi12_state.md` §"what remains" item 1 for the route.
-/

open scoped Pointwise NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.N2v2

/-- **The `g`-sum of the escape orthogonality.**
For the global unit `bg` whose Kummer character realises the datum `g` on `G_K`, and `c₁` whose
Kummer field lies in the level `E` and in the `↥K`-copy of `L₁`, the sum over `T'` of the
`χ_{c₁}`-values of the local Artin factors of `bg` vanishes. -/
theorem HeartGsumNarrow (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (L₁ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁] (hKL₁ : K ≤ L₁)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, _root_.SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hTcov : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : _root_.SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ _root_.SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ → g σ = 0)
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)]
    (hexpE : ∀ σ : ↥E ≃ₐ[↥K] ↥E, σ ^ p = 1)
    (θ : (v : NK.GlobalCFT.Place ↥K) →
      (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥E ≃ₐ[↥K] ↥E))
    (hθker : ∀ v, (θ v).ker = NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E) v)
    (hθprod : ∀ (x : (↥K)ˣ) (s : Finset (NK.GlobalCFT.Place ↥K)),
      (∀ v, v ∉ s → θ v (NK.CFTLib.IdeleHasse.localImageAt v x) = 1) →
      NK.CFTLib.IdeleHasse.cprod (fun a b => mul_comm' a b) s
        (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1)
    (hlift : ∀ (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
      (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
      ∀ x : (↥K)ˣ, ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ _root_.SSGRoute.decomp (k := ↥K) A ∧
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
          θ (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x))
    (hunith : ∀ (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
      (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
      ∀ u : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ,
        u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔭) →
        ∃ σ : Ω ≃ₐ[↥K] Ω, _root_.SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            θ (NK.GlobalCFT.Place.ofFinite 𝔭) u)
    (hgE : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ E.fixingSubgroup → g (σ.restrictScalars k) = 0)
    (bg : (↥K)ˣ)
    (hbg : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      g σ = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ bg
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (harchbg : ∀ w : NumberField.InfinitePlace ↥K,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) bg ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E)
          (NK.GlobalCFT.Place.ofInfinite w))
    (c₁ : (↥K)ˣ) (hc₁E : NK.LocalAnabelian.kummerField (K' := Ω) p c₁ ≤ E)
    (hc₁L : NK.LocalAnabelian.kummerField (K' := Ω) p c₁ ≤
      Work.SSGRoute.EscapeCoreLib.baseChange K L₁ hKL₁)
    (χE₁ : (↥E ≃ₐ[↥K] ↥E) →* Multiplicative (ZMod p))
    (hχE₁ : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χE₁ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ) =
        Multiplicative.ofAdd
          (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₁ σ)) :
    ∑ 𝔭 ∈ T', (χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg))).toAdd
      = 0 := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hSepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  have hψkill : ∀ σ ∈ L₁.fixingSubgroup, klevelKummer (Ω := Ω) p K ζ hζ c₁ σ = 0 :=
    klevelKummer_kill (Ω := Ω) p K ζ hζ c₁ L₁ hKL₁ hc₁L
  -- the ramified primes of `↥K`, and the support of the principal fractional ideal of `bg`
  set Sram : Finset (NK.Chebotarev.PrimeIdeal ↥K) :=
    ((Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
      (K := ↥K) (L := ↥E)).toFinset).image
      (fun q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E) =>
        ⟨q.asIdeal.under (NumberField.RingOfIntegers ↥K), inferInstance,
          Ideal.under_ne_bot _ q.ne_bot⟩) with hSram
  set Ssupp : Finset (NK.Chebotarev.PrimeIdeal ↥K) :=
    (FractionalIdeal.finite_factors (K := ↥K)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bg : ↥K))).toFinset with hSsupp
  set s : Finset (NK.Chebotarev.PrimeIdeal ↥K) := (T' ∪ Sram) ∪ Ssupp with hs
  -- off `Sram` the extension `E/↥K` is unramified
  have hunr : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ Sram →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) 𝔮 := by
    intro 𝔮 h𝔮 q hq
    by_contra hne
    refine h𝔮 (Finset.mem_image.mpr ⟨q, (Set.Finite.mem_toFinset _).mpr hne, ?_⟩)
    haveI := hq
    ext x
    rw [Ideal.over_def (P := q.asIdeal) (p := 𝔮.asIdeal)]
  -- the bridge between `exp` of the principal idèle and `count` of the principal ideal
  have hbridge : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      NK.GlobalCFT.Idele.exp 𝔮 (NK.GlobalCFT.Idele.principalIdele ↥K bg) =
        FractionalIdeal.count ↥K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (bg : ↥K)) := by
    intro 𝔮
    rw [NK.GlobalCFT.Idele.exp_principalIdele,
      NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq 𝔮 bg.ne_zero]
  -- off `s` the local factor is trivial
  have hst : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ s →
      θ (Place.ofFinite 𝔮) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔮) bg) = 1 := by
    intro 𝔮 h𝔮
    have h𝔮T : 𝔮 ∉ T' := fun h => h𝔮 (by rw [hs]; exact Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have h𝔮ram : 𝔮 ∉ Sram := fun h => h𝔮 (by rw [hs]; exact Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have h𝔮supp : 𝔮 ∉ Ssupp := fun h => h𝔮 (by rw [hs]; exact Finset.mem_union_right _ h)
    have hcount0 : FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (bg : ↥K)) = 0 := by
      by_contra hne
      exact h𝔮supp (by rw [hSsupp]; exact (Set.Finite.mem_toFinset _).mpr hne)
    have hexp0 : NK.GlobalCFT.Idele.exp 𝔮 (NK.GlobalCFT.Idele.principalIdele ↥K bg) = 0 := by
      rw [hbridge 𝔮, hcount0]
    have hunit : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg ∈
        NK.GlobalCFT.Place.localUnits ↥K (Place.ofFinite 𝔮) :=
      (NK.NUV2.RouteB.RayModulus.mem_localUnits_iff_exp_eq_zero 𝔮
        (NK.GlobalCFT.Idele.principalIdele ↥K bg)).mpr hexp0
    rw [← MonoidHom.mem_ker, hθker]
    exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified (K := ↥K) (L := ↥E)
      𝔮 (hunr 𝔮 h𝔮ram) hunit
  -- the product formula over `s`
  have hsum0 : ∑ 𝔮 ∈ s, (χE₁ (θ (Place.ofFinite 𝔮)
      (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔮) bg))).toAdd = 0 :=
    sum_localFactors_eq_zero p (fun a b => mul_comm' a b) χE₁ θ hθprod bg
      (fun w => by
        have hmem : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) bg ∈
            (θ (Place.ofInfinite w)).ker := by
          rw [hθker (Place.ofInfinite w)]
          exact harchbg w
        rw [MonoidHom.mem_ker.mp hmem]
        simp)
      s hst
  -- the terms at places of `s` outside `T'` vanish individually
  have houter : ∀ 𝔮 ∈ s \ T', (χE₁ (θ (Place.ofFinite 𝔮)
      (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔮) bg))).toAdd = 0 := by
    intro 𝔮 h𝔮
    have h𝔮s : 𝔮 ∈ s := (Finset.mem_sdiff.mp h𝔮).1
    have h𝔮T : 𝔮 ∉ T' := (Finset.mem_sdiff.mp h𝔮).2
    obtain ⟨B, hBcomap, hBfin⟩ := exists_isFinPlace_comap_eq (k := k) (Ω := Ω) K 𝔮
    have hnoT : ∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B := by
      intro A hAT τ hτ hconj
      obtain ⟨𝔭A, h𝔭AT', h𝔭Aeq⟩ := hTbelow A hAT
      have hsmul : ((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩ : Ω ≃ₐ[↥K] Ω) • A = τ • A := by
        apply ValuationSubring.ext
        intro x
        rw [ValuationSubring.mem_smul_pointwise_iff_exists,
          ValuationSubring.mem_smul_pointwise_iff_exists]
        constructor <;> rintro ⟨s, hs, hx⟩ <;>
          exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl⟩
      have h1 : B.comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
        rw [← hconj, ← hsmul, SSGRoute.comap_algebraMap_smul]
      rw [hBcomap, h𝔭Aeq] at h1
      exact h𝔮T (by
        have hthis := Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
          (R := NumberField.RingOfIntegers ↥K) (K := ↥K) h1
        exact hthis ▸ h𝔭AT')
    by_cases hsplit : SSGRoute.IsSplitIn k L₁ B
    · -- `B` splits completely in `L₁`
      obtain ⟨σ, hσdec, hσeq⟩ := hlift B hBfin 𝔮 hBcomap bg
      have hσ'dec : σ.restrictScalars k ∈ SSGRoute.decomp k B :=
        restrictScalars_mem_decomp K hσdec
      have hχ : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₁ σ = 0 := by
        rw [← klevelKummer_restrictScalars (Ω := Ω) p K ζ hζ c₁ σ]
        exact hψkill (σ.restrictScalars k) (hsplit hσ'dec)
      rw [← hσeq, hχE₁ σ, hχ]
      rfl
    · -- `hgram` applies
      have hgramB : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0 :=
        hgram B hBfin hnoT hsplit
      have hchar : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
          SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ bg
            ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) = 0 := by
        intro σ hσ hinert
        rw [← hbg σ hσ]
        exact hgramB σ hσ hinert
      obtain ⟨b, u, hu, hdec⟩ :=
        localImageAt_eq_pow_mul_localUnits_of_inertia p k Ω K ζ hζ B hBfin 𝔮 hBcomap bg hchar
      obtain ⟨σu, hσu_inertia, hσu_eq⟩ := hunith B hBfin 𝔮 hBcomap u hu
      have hIB : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
          SSGRoute.IsInertia k B σ → σ ∈ L₁.fixingSubgroup := by
        intro σ hσ hinert
        by_contra hnot
        obtain ⟨A, hAT, τ, hτ, hconj⟩ := hTcov B hBfin (Or.inr ⟨σ, hσ, hinert, hnot⟩)
        exact hnoT A hAT τ hτ hconj
      have hσuK : σu.restrictScalars k ∈ K.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact σu.commutes ⟨x, hx⟩
      have hpow : θ (Place.ofFinite 𝔮) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔮) bg) =
          θ (Place.ofFinite 𝔮) u := by
        rw [hdec, map_mul, map_pow, hexpE (θ (Place.ofFinite 𝔮) b), one_mul]
      rw [hpow, ← hσu_eq, hχE₁ σu, ← klevelKummer_restrictScalars (Ω := Ω) p K ζ hζ c₁ σu]
      exact hψkill (σu.restrictScalars k) (hIB (σu.restrictScalars k) hσuK hσu_inertia)
  -- split the sum
  have hsub : T' ⊆ s := by
    intro 𝔭 h𝔭
    rw [hs]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ h𝔭)
  have hsdiff : ∑ 𝔮 ∈ s \ T', (χE₁ (θ (Place.ofFinite 𝔮)
      (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔮) bg))).toAdd = 0 :=
    Finset.sum_eq_zero houter
  have hsd := Finset.sum_sdiff
      (f := fun 𝔮 => (χE₁ (θ (Place.ofFinite 𝔮)
        (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔮) bg))).toAdd) hsub
  rw [← hsum0, ← hsd, hsdiff, zero_add]

end Work.SSGRoute.N2v2
