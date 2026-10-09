import Mathlib
import Submission.Work.SSGRoute.N2v2.heart_chi1_part
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.myv2

/-- **The `g`-sum of the escape orthogonality**: for the global unit `bg` whose Kummer character
realises the datum `g` on `G_K`, and `c₁` whose Kummer field lies in the level `E` and in the `↥K`-copy
of `L₁`, the sum over `T'` of the `χ_{c₁}`-values of the local Artin factors of `bg` vanishes.

Route: the product formula `N2v2.sum_localFactors_eq_zero` for the pair `(χE₁, θ)` and the element
`bg` over the finite set `s = T' ∪ Sram ∪ Ssupp` (where `Sram` contains the primes ramified in `E/↥K`
and `Ssupp` the support of `bg`), all places off `s` having trivial local factor, and each place of
`s \ T'` contributing `0` individually: either the place splits in `L₁` (then `hlift` gives a lift in
the decomposition group, killed by `χE₁` because it factors through `L₁`), or `hgram` makes `g` kill
the inertia, so `bg` is locally a `p`-th power times a unit
(`ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified`), `θ` of the `p`-th power
dies by `hexpE` and `hunith` lifts `θ` of the unit into the inertia, which `χE₁` kills because
`hTcov` forces `L₁` to be unramified at a place outside the classes of `T`. -/
theorem gsum_vanishes (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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
    (harch : ∀ v : NK.GlobalCFT.Place ↥K, (∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
        v ≠ NK.GlobalCFT.Place.ofFinite 𝔮) →
      ∀ u : (NK.GlobalCFT.Place.localField ↥K v)ˣ, θ v u = 1)
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
  haveI hNumE : NumberField ↥E := NumberField.of_module_finite ↥K ↥E
  -- ### 0. `L₁`-fixing automorphisms kill the Kummer character of `c₁`
  have hkillL₁ : ∀ σ : Ω ≃ₐ[↥K] Ω, σ.restrictScalars k ∈ L₁.fixingSubgroup →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₁ σ = 0 := by
    intro σ hσ
    rw [← Work.SSGRoute.N2v2.klevelKummer_restrictScalars (Ω := Ω) p K ζ hζ c₁ σ]
    exact Work.SSGRoute.N2v2.klevelKummer_kill (Ω := Ω) p K ζ hζ c₁ L₁ hKL₁ hc₁L
      (σ.restrictScalars k) hσ
  -- ### 1. the finite sets `Sram` (ramified in `E/↥K`) and `Ssupp` (support of `bg`)
  set Sram : Finset (NK.Chebotarev.PrimeIdeal ↥K) :=
    (NK.HeckeL.Basic.finite_setOf_not_isUnramifiedIn (K := ↥K) (L := ↥E)).toFinset with hSram
  set Ssupp : Finset (NK.Chebotarev.PrimeIdeal ↥K) :=
    (NK.GlobalCFT.Idele.finite_exp_support
      (NK.GlobalCFT.Idele.principalIdele ↥K bg)).toFinset with hSsupp
  set s : Finset (NK.Chebotarev.PrimeIdeal ↥K) := T' ∪ Sram ∪ Ssupp with hsdef
  have hmemSram : ∀ 𝔮, 𝔮 ∈ Sram ↔ ¬ NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) 𝔮 := by
    intro 𝔮
    rw [hSram]
    exact Set.Finite.mem_toFinset _
  have hmemSsupp : ∀ 𝔮, 𝔮 ∈ Ssupp ↔
      NK.GlobalCFT.Idele.exp 𝔮 (NK.GlobalCFT.Idele.principalIdele ↥K bg) ≠ 0 := by
    intro 𝔮
    rw [hSsupp]
    exact Set.Finite.mem_toFinset _
  -- ### 2. off `s` the local factor is trivial
  have hs : ∀ 𝔮, 𝔮 ∉ s → θ (Place.ofFinite 𝔮)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg) = 1 := by
    intro 𝔮 h𝔮
    have h𝔮ram : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) 𝔮 := by
      by_contra h
      exact h𝔮 (by
        rw [hsdef]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ ((hmemSram 𝔮).mpr h)))
    have h𝔮supp : NK.GlobalCFT.Idele.exp 𝔮 (NK.GlobalCFT.Idele.principalIdele ↥K bg) = 0 := by
      by_contra h
      exact h𝔮 (by
        rw [hsdef]
        exact Finset.mem_union_right _ ((hmemSsupp 𝔮).mpr h))
    have hloc : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg ∈
        Place.localUnits ↥K (Place.ofFinite 𝔮) := by
      rw [← Work.SSGRoute.ZDataMup.principalIdele_apply_eq_localImageAt (K := ↥K) bg
        (Place.ofFinite 𝔮)]
      exact (NK.NUV2.RouteB.RayModulus.mem_localUnits_iff_exp_eq_zero 𝔮
        (NK.GlobalCFT.Idele.principalIdele ↥K bg)).mpr h𝔮supp
    rw [← MonoidHom.mem_ker, hθker]
    exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified (K := ↥K) (L := ↥E)
      𝔮 h𝔮ram hloc
  -- ### 3. the product formula for the pair `(χE₁, θ)` and the element `bg`
  have harch' : ∀ w : NumberField.InfinitePlace ↥K,
      (χE₁ (θ (Place.ofInfinite w)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) bg))).toAdd = 0 := by
    intro w
    rw [harch (Place.ofInfinite w) (fun 𝔮 => Place.ofInfinite_ne_ofFinite w 𝔮) _, map_one]
    rfl
  have hsum0 : (∑ 𝔮 ∈ s, (χE₁ (θ (Place.ofFinite 𝔮)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg))).toAdd) = 0 :=
    Work.SSGRoute.N2v2.sum_localFactors_eq_zero (K := ↥K) (L := ↥E) p
      (fun a b => mul_comm' a b) χE₁ θ hθprod bg harch' s hs
  -- ### 4. every place outside `T'` contributes `0`
  have hvan : ∀ 𝔮 ∈ s \ T', (χE₁ (θ (Place.ofFinite 𝔮)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg))).toAdd = 0 := by
    intro 𝔮 h𝔮
    have h𝔮T : 𝔮 ∉ T' := (Finset.mem_sdiff.mp h𝔮).2
    obtain ⟨B, hBcomap, hBfin⟩ := Work.SSGRoute.exists_isFinPlace_comap_eq (k := k) (Ω := Ω) K 𝔮
    by_cases hsplit : SSGRoute.IsSplitIn k L₁ B
    · -- the place splits in `L₁`: the lift of `hlift` lies in the decomposition group, so it is
      -- killed by the Kummer character of `c₁`
      obtain ⟨σ, hσdec, hσeq⟩ := hlift B hBfin 𝔮 hBcomap bg
      have hσrest : σ.restrictScalars k ∈ L₁.fixingSubgroup :=
        hsplit (Work.SSGRoute.N2v2.restrictScalars_mem_decomp K hσdec)
      rw [← hσeq, hχE₁ σ]
      exact hkillL₁ σ hσrest
    · -- otherwise `hgram` kills the inertia
      have hnotconj : ∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B := by
        intro A hA τ hτ heq
        obtain ⟨𝔭, h𝔭T, h𝔭comap⟩ := hTbelow A hA
        have h1 : B.comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
          rw [← heq]
          exact Work.SSGRoute.comap_smul_eq_of_mem_fixingSubgroup K hτ A
        have h2 : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 =
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
          rw [← hBcomap, h1, h𝔭comap]
        exact h𝔮T (by
          rw [Commons.RingTheory.Valuation.valuationSubringAtPrime_injective h2]
          exact h𝔭T)
      have hchar : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ bg
            ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) = 0 := by
        intro σ hσ hinert
        rw [← hbg σ hσ]
        exact hgram B hBfin hnotconj hsplit σ hσ hinert
      obtain ⟨b, u, hu, hdec⟩ := Work.SSGRoute.N2v2.localImageAt_eq_pow_mul_localUnits_of_inertia
        p k Ω K ζ hζ B hBfin 𝔮 hBcomap bg hchar
      obtain ⟨σu, hσu_inertia, hσu_eq⟩ := hunith B hBfin 𝔮 hBcomap u hu
      -- `hTcov` forces the inertia of `B` into `L₁`
      have hinertsub : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ K.fixingSubgroup → SSGRoute.IsInertia k B σ →
          σ ∈ L₁.fixingSubgroup := by
        intro σ hσ hinert
        by_contra hσL
        obtain ⟨A, hA, τ, hτ, hτA⟩ := hTcov B hBfin (Or.inr ⟨σ, hσ, hinert, hσL⟩)
        exact hnotconj A hA τ hτ hτA
      have hσuK : σu.restrictScalars k ∈ K.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact σu.commutes ⟨x, hx⟩
      have hσuL : σu.restrictScalars k ∈ L₁.fixingSubgroup :=
        hinertsub _ hσuK hσu_inertia
      have hpow : θ (Place.ofFinite 𝔮)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg) =
          θ (Place.ofFinite 𝔮) u := by
        rw [hdec, map_mul, map_pow, hexpE (θ (Place.ofFinite 𝔮) b), one_mul]
      rw [hpow, ← hσu_eq, hχE₁ σu]
      exact hkillL₁ σu hσuL
  -- ### 5. assembly
  have hsub : T' ⊆ s := by
    intro 𝔮 h𝔮
    rw [hsdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ h𝔮)
  have hsd0 : (∑ 𝔮 ∈ s \ T', (χE₁ (θ (Place.ofFinite 𝔮)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg))).toAdd) = 0 :=
    Finset.sum_eq_zero hvan
  have h3 := Finset.sum_sdiff (f := fun 𝔮 => (χE₁ (θ (Place.ofFinite 𝔮)
    (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) bg))).toAdd) hsub
  rw [hsd0, hsum0] at h3
  simpa using h3

end Work.SSGRoute.myv2
