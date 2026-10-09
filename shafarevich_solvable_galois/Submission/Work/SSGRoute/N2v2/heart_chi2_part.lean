import Mathlib
import Submission.Work.SSGRoute.N2v2.char_eq_neg_localSum
import Submission.Work.SSGRoute.N2v2.kummerField_le_of_vanishes_on_fixingSubgroup
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.ZConstruction.kummerCharZModAdd
import Submission.Work.SSGRoute.EscapeCoreLib.baseChange_over_K
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `χ₂`-part of the escape orthogonality

Per place of `T'`, the trichotomy `horth₂` kills the `χ_{c₂}`-component of the local Artin factor of
the Grünwald element `a`.  The three cases are: (i) the datum `g + hA` vanishes on the decomposition
group `D_A`, so `a_𝔭` is a local `p`-th power (local Kummer dictionary) and `θ(a_𝔭) = θ(γ)^p = 1`
because `Gal(E/↥K)` has exponent `p`; (ii) every character killing `L₂.fixingSubgroup` kills `D_A`,
and the Kummer character of `c₂` is such a character; (iii) the datum kills the inertia `I_A`, so the
local image of `a` is a `p`-th power times a local unit, whose local Artin factor has a lift in `I_A`
(`hunith`) which the Kummer character of `c₂` kills.
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.N2v2

/-- **The Kummer character vanishes on the fixing subgroup of any field containing its Kummer
field.** -/
theorem kummerCharZMod_eq_zero_of_kummerField_le (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (c : (↥K)ˣ)
    (L : IntermediateField ↥K Ω)
    (h : NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ L)
    (σ : Ω ≃ₐ[↥K] Ω) (hσ : σ ∈ L.fixingSubgroup) :
    Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ = 0 := by
  have hαmem : Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p c ∈
      NK.LocalAnabelian.kummerField (K' := Ω) p c := by
    rw [NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple p Fact.out hζ c
      (Work.SSGRoute.kummerSqrtZMod_pow (Ω := Ω) p c)]
    exact IntermediateField.mem_adjoin_simple_self _ _
  rw [Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt p hζ c σ]
  exact (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ _ (h hαmem)

/-- The restriction to `k` of a `↥K`-decomposition element is a `k`-decomposition element. -/
theorem restrictScalars_mem_decomp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {A : ValuationSubring Ω} {σ : Ω ≃ₐ[↥K] Ω}
    (hσ : σ ∈ SSGRoute.decomp (k := ↥K) A) :
    σ.restrictScalars k ∈ SSGRoute.decomp k A := by
  have hsmul : (σ.restrictScalars k : Ω ≃ₐ[k] Ω) • A = σ • A := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists,
      ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor <;> rintro ⟨s, hs, hx⟩ <;>
      exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl⟩
  rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff] at hσ ⊢
  rw [hsmul, hσ]

/-- The `↥K`-image of the restriction to `k` of a `↥K`-automorphism is that automorphism itself. -/
theorem fixingSubgroupEquiv_restrictScalars {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (σ : Ω ≃ₐ[↥K] Ω) :
    (IntermediateField.fixingSubgroupEquiv K)
        ⟨σ.restrictScalars k, by
          rw [IntermediateField.mem_fixingSubgroup_iff]
          intro x hx
          exact σ.commutes ⟨x, hx⟩⟩ = σ := by
  ext x
  rfl

/-- **The `p`-unit form of the arithmetic input**: if the Kummer character of `c` vanishes on the
inertia of `A`, then the local image of `c` is a `p`-th power times a local unit. -/
theorem localImageAt_eq_pow_mul_localUnits_of_inertia (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥K)
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (c : (↥K)ˣ)
    (h : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k A σ →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) = 0) :
    ∃ b : (Place.localField ↥K (Place.ofFinite 𝔭))ˣ,
      ∃ u ∈ Place.localUnits ↥K (Place.ofFinite 𝔭),
        NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) c = b ^ p * u := by
  obtain ⟨γ, u, hu, hdec⟩ :=
    ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified
      p k Ω K ζ hζ A hA 𝔭 h𝔭 c h
  exact ⟨γ, u, hu, hdec⟩

/-- The `n`-th power of a one-place idèle. -/
theorem onePlace_pow_aux {K : Type} [Field K] [NumberField K] (w : Place K)
    (u : (Place.localField K w)ˣ) (n : ℕ) :
    NK.HassePrinciple.onePlace w (u ^ n) = (NK.HassePrinciple.onePlace w u) ^ n := by
  rw [← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := K) w (u ^ n),
    ← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := K) w u, map_pow]

/-- A vanishing local `p`-th power class means the local component is a `p`-th power. -/
theorem localImageAt_mem_powRange_of_localPowClass_eq_one {K : Type} [Field K] [NumberField K]
    (p : ℕ) (𝔮 : NK.Chebotarev.PrimeIdeal K) (γ : Kˣ)
    (hγ : NK.UchidaKummer.localPowClass K p 𝔮 γ = 1) :
    NK.CFTLib.IdeleHasse.localImageAt (K := K) (Place.ofFinite 𝔮) γ ∈
      (powMonoidHom p : ((𝔮.adicCompletion K)ˣ →* (𝔮.adicCompletion K)ˣ)).range := by
  have h := hγ
  rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h
  exact (QuotientGroup.eq_one_iff _).mp h

/-- **The `χ₂`-part of the escape orthogonality**: for `c₂` whose Kummer field lies in the level `E`
and in the `↥K`-copy of `L₂`, the sum over `T'` of the `χ_{c₂}`-values of the local Artin factors of
the Grünwald element `a` vanishes. -/
theorem heart_chi2_part (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (L₂ : IntermediateField k Ω) [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, _root_.SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → χ σ = 0))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)]
    (hexpE : ∀ σ : ↥E ≃ₐ[↥K] ↥E, σ ^ p = 1)
    (θ : (v : NK.GlobalCFT.Place ↥K) →
      (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥E ≃ₐ[↥K] ↥E))
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
    (c₂ : (↥K)ˣ) (hc₂E : NK.LocalAnabelian.kummerField (K' := Ω) p c₂ ≤ E)
    (hc₂L : NK.LocalAnabelian.kummerField (K' := Ω) p c₂ ≤
      Work.SSGRoute.EscapeCoreLib.baseChange K L₂ hKL₂)
    (χE₂ : (↥E ≃ₐ[↥K] ↥E) →* Multiplicative (ZMod p))
    (hχE₂ : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χE₂ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ) =
        Multiplicative.ofAdd
          (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₂ σ)) :
    ∑ 𝔭 ∈ T', (χE₂ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd
      = 0 := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hSepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  -- the `k`-level extension of the Kummer character of `c₂`
  let ψ : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ =>
    if h : σ ∈ K.fixingSubgroup then
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₂
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, h⟩)
    else 0
  have hψadd : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, ψ (x * y) = ψ x + ψ y := by
    intro x hx y hy
    have hxy : x * y ∈ K.fixingSubgroup := Subgroup.mul_mem _ hx hy
    have hmul : ((IntermediateField.fixingSubgroupEquiv K) ⟨x * y, hxy⟩ : Ω ≃ₐ[↥K] Ω) =
        ((IntermediateField.fixingSubgroupEquiv K) ⟨x, hx⟩) *
          ((IntermediateField.fixingSubgroupEquiv K) ⟨y, hy⟩) := by
      rw [← map_mul]
      rfl
    simp only [ψ, dif_pos hx, dif_pos hy, dif_pos hxy]
    rw [hmul, Work.SSGRoute.ZConstruction.kummerCharZMod_apply_mul ζ hζ c₂]
  -- `ψ` kills the fixing subgroup of `L₂`
  have hψkill : ∀ σ ∈ L₂.fixingSubgroup, ψ σ = 0 := by
    intro σ hσ
    have hσK : σ ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
      intro x hx
      exact hσ x (hKL₂ hx)
    have hbase : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩) ∈
        (Work.SSGRoute.EscapeCoreLib.baseChange K L₂ hKL₂).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hxL : x ∈ L₂ := (Work.SSGRoute.EscapeCoreLib.mem_baseChange K L₂ hKL₂).mp hx
      have hfix : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ : Ω ≃ₐ[↥K] Ω) x =
          σ x := rfl
      rw [hfix]
      exact (IntermediateField.mem_fixingSubgroup_iff L₂ σ).mp hσ x hxL
    simp only [ψ, dif_pos hσK]
    exact kummerCharZMod_eq_zero_of_kummerField_le p k Ω K ζ hζ c₂
      (Work.SSGRoute.EscapeCoreLib.baseChange K L₂ hKL₂) hc₂L _ hbase
  -- `ψ` of the restriction of a `↥K`-lift
  have hψlift : ∀ σ : Ω ≃ₐ[↥K] Ω,
      ψ (σ.restrictScalars k) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₂ σ := by
    intro σ
    have hσK : σ.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    simp only [ψ, dif_pos hσK]
    rw [fixingSubgroupEquiv_restrictScalars K σ]
  refine Finset.sum_eq_zero (fun 𝔭 h𝔭 => ?_)
  obtain ⟨A, hAT, hAcomap⟩ := hT'above 𝔭 h𝔭
  have hAfin : SSGRoute.IsFinPlace k A := hTfin A hAT
  rcases horth₂ A hAT with hcase | hcase | hcase
  · -- ## case (i): the datum vanishes on `D_A`
    have hchar : ∀ τ : Ω ≃ₐ[↥K] Ω, τ ∈ SSGRoute.decomp (k := ↥K) A →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a τ = 0 := by
      intro τ hτ
      have hτ'K : τ.restrictScalars k ∈ K.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact τ.commutes ⟨x, hx⟩
      have hτ'dec : τ.restrictScalars k ∈ SSGRoute.decomp k A :=
        restrictScalars_mem_decomp K hτ
      have h1 : g (τ.restrictScalars k) + h A (τ.restrictScalars k) = 0 :=
        hcase _ ⟨hτ'dec, hτ'K⟩
      have h2 := ha A hAT ⟨τ.restrictScalars k, ⟨hτ'dec, hτ'K⟩⟩
      have h3 : Work.SSGRoute.gesLocalToGalK K ⟨τ.restrictScalars k, ⟨hτ'dec, hτ'K⟩⟩ = τ :=
        fixingSubgroupEquiv_restrictScalars K τ
      rw [h3] at h2
      rw [← h2, h1]
    have hlp : NK.UchidaKummer.localPowClass ↥K p 𝔭 a = 1 :=
      (Work.SSGRoute.local_kummer_dictionary (k := k) (Ω := Ω) p K ζ hζ A hAfin 𝔭 hAcomap
        a).mp hchar
    obtain ⟨b, hb⟩ := localImageAt_mem_powRange_of_localPowClass_eq_one p 𝔭 a hlp
    have hpow : θ (Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a) = 1 := by
      rw [show NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a = b ^ p from
        hb.symm, map_pow, hexpE (θ (Place.ofFinite 𝔭) b)]
    rw [hpow, map_one]
    rfl
  · -- ## case (ii): every character killing `L₂.fixingSubgroup` kills `D_A`
    obtain ⟨σ, hσdec, hσeq⟩ := hlift A hAfin 𝔭 hAcomap a
    have hσ'K : σ.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    have hzero : ψ (σ.restrictScalars k) = 0 :=
      hcase ψ hψadd hψkill _ ⟨restrictScalars_mem_decomp K hσdec, hσ'K⟩
    have hkey : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₂ σ = 0 := by
      rw [← hψlift σ]
      exact hzero
    rw [← hσeq, hχE₂ σ, hkey]
    rfl
  · -- ## case (iii): the datum kills the inertia
    obtain ⟨hc1, hc2⟩ := hcase
    have hchar : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
        SSGRoute.IsInertia k A σ →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) = 0 := by
      intro σ hσ hinert
      have hσdec : σ ∈ SSGRoute.decomp k A := hinert.1
      have h2 := ha A hAT ⟨σ, ⟨hσdec, hσ⟩⟩
      have h3 : Work.SSGRoute.gesLocalToGalK K ⟨σ, ⟨hσdec, hσ⟩⟩ =
          (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ := rfl
      rw [h3] at h2
      rw [← h2]
      exact hc1 σ hσ hinert
    obtain ⟨b, u, hu, hdec⟩ :=
      localImageAt_eq_pow_mul_localUnits_of_inertia p k Ω K ζ hζ A hAfin 𝔭 hAcomap a hchar
    -- the local factor of the unit part has a lift in the inertia
    obtain ⟨σu, hσu_inertia, hσu_eq⟩ := hunith A hAfin 𝔭 hAcomap u hu
    have hσuK : σu.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σu.commutes ⟨x, hx⟩
    have hzero : ψ (σu.restrictScalars k) = 0 :=
      hc2 ψ hψadd hψkill (σu.restrictScalars k) hσuK hσu_inertia
    have hkey : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₂ σu = 0 := by
      rw [← hψlift σu]
      exact hzero
    have hpow : θ (Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a) =
        θ (Place.ofFinite 𝔭) u := by
      rw [hdec, map_mul, map_pow, hexpE (θ (Place.ofFinite 𝔭) b), one_mul]
    rw [hpow, ← hσu_eq, hχE₂ σu, hkey]
    rfl

end Work.SSGRoute.N2v2
