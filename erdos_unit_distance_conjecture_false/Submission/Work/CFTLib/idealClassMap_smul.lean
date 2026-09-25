import Mathlib
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.NKIdeles
import Submission.Work.CFTLib.IdealPrimeMap

/-!
# The ideal class map commutes with the Galois action on idèles

For a finite Galois extension `K/F` of number fields and `σ : Gal(K/F)`, the canonical action on
the idèle group `𝕀 K` (namely `(σ · x)_w = σ_*(x_{σ⁻¹ w})`, where `σ_*` is the local field
isomorphism at the place `w`) is compatible with the ideal class map `𝕀 K →* Cl(𝓞 K)`: the ideal
class of the translate `σ · x` is the transport of the ideal class of `x` along the automorphism
of the class group induced by `σ`.

The proof has two ingredients:

* the Galois action on idèles multiplies the `q`-adic exponent of the associated fractional ideal
  by moving the place `q` to `σ · q` (`NK.GlobalCFT.Idele.exp_smul`), which rests on the fact that
  the local field isomorphism `K_q ≃+* K_{σ q}` is an isometry for the local valuations;
* the transported fractional ideal `σ_*(I)` has counts `count q (σ_*(I)) = count (σ⁻¹ q) I`.

## Main results

* `Work.CFTLib.valued_mapRingEquiv_completion`: the completion of an isometry of valued fields
  preserves the extended valuation;
* `NK.GlobalCFT.Idele.valued_adicCongrEquiv`: the local isomorphism `K_q ≃+* K_{σ q}` is an
  isometry;
* `NK.GlobalCFT.Idele.exp_smul`: `exp q (σ · x) = exp (σ⁻¹ q) x`;
* `NK.GlobalCFT.Idele.idealOf_smul`: the fractional ideal of `σ · x` is the transport of the
  fractional ideal of `x`;
* `Work.CFTLib.IdealClassMapAux.count_ringEquivOfRingEquiv`,
  `Work.CFTLib.IdealClassMapAux.mulEquiv_mk`: the transport of counts and of ideal classes along a
  ring equivalence of `𝓞 K`;
* `Work.CFTLib.idealClassMap_smul`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped WithZeroTopology nonZeroDivisors
open NumberField IsDedekindDomain MonoidWithZeroHom

noncomputable section

namespace Work.CFTLib

/-! ## Isometries of completions of valued fields

The completion `hat K` of a valued field `K` carries the extended valuation `Valued.v`.  If
`F : WithVal v ≃+* WithVal w` is a ring isomorphism which preserves the valuations pointwise, then
so does its extension to the completions. -/

set_option maxHeartbeats 4000000 in
/-- **An isometry of valued fields preserves the extended valuation.**  If
`F : WithVal v ≃+* WithVal w` preserves the values of the two valuations, then the induced ring
isomorphism of completions `(v).Completion ≃+* (w).Completion` does too. -/
theorem valued_mapRingEquiv_completion {R S Γ₀ : Type} [Field R] [Field S]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (w : Valuation S Γ₀) (F : WithVal v ≃+* WithVal w)
    (hF : ∀ y : WithVal v, Valued.v (F y) = Valued.v y)
    (hv : Function.Surjective (Valued.v : WithVal v → Γ₀))
    (hw : Function.Surjective (Valued.v : WithVal w → Γ₀))
    (h₁ : Continuous F) (h₂ : Continuous F.symm) (x : (v).Completion) :
    Valued.v ((UniformSpace.Completion.mapRingEquiv F h₁ h₂) x) = Valued.v x := by
  have hcontV : Continuous (Valued.v : (v).Completion → Γ₀) :=
    Valued.continuous_valuation_of_surjective
      ((Valued.valuedCompletion_surjective_iff (K := WithVal v)).mpr hv)
  have hcontW : Continuous (Valued.v : (w).Completion → Γ₀) :=
    Valued.continuous_valuation_of_surjective
      ((Valued.valuedCompletion_surjective_iff (K := WithVal w)).mpr hw)
  have hdense : Dense (Set.range (fun y : WithVal v => (y : (v).Completion))) :=
    UniformSpace.Completion.denseRange_coe
  have hΦ : Continuous (fun x : (v).Completion =>
      (UniformSpace.Completion.mapRingEquiv F h₁ h₂) x) := by
    rw [show (fun x : (v).Completion => (UniformSpace.Completion.mapRingEquiv F h₁ h₂) x)
      = UniformSpace.Completion.map (⇑F) from funext fun x => by
        rw [UniformSpace.Completion.mapRingEquiv_apply]]
    exact UniformSpace.Completion.continuous_map
  have hΦC : Continuous (fun x : (v).Completion =>
      Valued.v ((UniformSpace.Completion.mapRingEquiv F h₁ h₂) x)) := by
    rw [show (fun x : (v).Completion =>
        Valued.v ((UniformSpace.Completion.mapRingEquiv F h₁ h₂) x))
      = (fun x : (w).Completion => Valued.v x) ∘
        (fun x : (v).Completion => (UniformSpace.Completion.mapRingEquiv F h₁ h₂) x) from rfl]
    exact hcontW.comp hΦ
  refine congr_fun (Continuous.ext_on (Y := (v).Completion) (X := Γ₀)
      (s := Set.range (fun y : WithVal v => (y : (v).Completion)))
      (f := fun x : (v).Completion =>
        Valued.v ((UniformSpace.Completion.mapRingEquiv F h₁ h₂) x))
      (g := fun x : (v).Completion => Valued.v x) hdense hΦC hcontV ?_) x
  rintro z ⟨y, rfl⟩
  show Valued.v ((UniformSpace.Completion.mapRingEquiv F h₁ h₂) (y : (v).Completion))
      = Valued.v (y : (v).Completion)
  have hcoe : (UniformSpace.Completion.mapRingEquiv F h₁ h₂) (y : (v).Completion)
      = (F y : (w).Completion) :=
    UniformSpace.Completion.mapRingHom_coe (f := F.toRingHom) (hf := h₁) y
  rw [hcoe, Valued.valuedCompletion_apply, Valued.valuedCompletion_apply]
  exact hF y

end Work.CFTLib

namespace Work.CFTLib.IdealClassMapAux

/-! ## The `count` of a transported fractional ideal

The transport of fractional ideals along a ring equivalence `e : 𝓞 K ≃+* 𝓞 K` moves the `q`-adic
counts of a fractional ideal to the transported prime `primeMap e q = e⁻¹ q`. -/

open Work.CFTLib

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Transporting an integral ideal along `e` transports its `q`-adic counts**: the multiplicity
of the prime `w` in `Ideal.map e J` is the multiplicity of `e⁻¹ w` in `J`. -/
theorem count_coe_map (e : R ≃+* R) (J : Ideal R) (hJ : J ≠ 0) (w : IsDedekindDomain.HeightOneSpectrum R) :
    FractionalIdeal.count K w ((Ideal.map (e : R →+* R) J : Ideal R) : FractionalIdeal R⁰ K)
      = FractionalIdeal.count K (primeMap e w) (J : FractionalIdeal R⁰ K) := by
  have hJmap : Ideal.map (e : R →+* R) J ≠ 0 := fun h =>
    hJ ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)
  rw [FractionalIdeal.count_coe K w hJmap,
    FractionalIdeal.count_coe K (primeMap e w) hJ]
  congr 1
  have hp1 : Irreducible (Associates.mk w.asIdeal) := Associates.irreducible_mk.mpr w.irreducible
  have hp2 : Irreducible (Associates.mk (primeMap e w).asIdeal) :=
    Associates.irreducible_mk.mpr (primeMap e w).irreducible
  have hm1 : Associates.mk (Ideal.map (e : R →+* R) J) ≠ 0 := Associates.mk_ne_zero.mpr hJmap
  have hm2 : Associates.mk J ≠ 0 := Associates.mk_ne_zero.mpr hJ
  have hcomap : ∀ k : ℕ, Ideal.comap (e : R →+* R) (w.asIdeal ^ k)
      = (primeMap e w).asIdeal ^ k := by
    intro k
    rw [show Ideal.comap (e : R →+* R) (w.asIdeal ^ k)
        = Ideal.map (e.symm : R →+* R) (w.asIdeal ^ k) from
      (Ideal.map_symm (I := w.asIdeal ^ k) e).symm, Ideal.map_pow]
    exact congrArg (fun I => I ^ k) (primeMap_asIdeal_map e w).symm
  have hiff : ∀ k : ℕ, (Associates.mk w.asIdeal) ^ k ≤ Associates.mk (Ideal.map (e : R →+* R) J)
      ↔ (Associates.mk (primeMap e w).asIdeal) ^ k ≤ Associates.mk J := by
    intro k
    rw [← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.dvd_iff_le,
      Ideal.map_le_iff_le_comap, hcomap k]
  refine le_antisymm ?_ ?_
  · have h1 : (Associates.mk w.asIdeal) ^ ((Associates.mk w.asIdeal).count
        (Associates.mk (Ideal.map (e : R →+* R) J)).factors) ≤
        Associates.mk (Ideal.map (e : R →+* R) J) :=
      (Associates.prime_pow_dvd_iff_le hm1 hp1).mpr le_rfl
    exact (Associates.prime_pow_dvd_iff_le hm2 hp2).mp ((hiff _).mp h1)
  · have h1 : (Associates.mk (primeMap e w).asIdeal) ^
        ((Associates.mk (primeMap e w).asIdeal).count (Associates.mk J).factors) ≤
        Associates.mk J :=
      (Associates.prime_pow_dvd_iff_le hm2 hp2).mpr le_rfl
    exact (Associates.prime_pow_dvd_iff_le hm1 hp1).mp ((hiff _).mpr h1)

/-- **The transport of fractional ideals is compatible with the `q`-adic counts.** -/
theorem count_ringEquivOfRingEquiv (e : R ≃+* R) (I : FractionalIdeal R⁰ K)
    (w : IsDedekindDomain.HeightOneSpectrum R) :
    FractionalIdeal.count K w (FractionalIdeal.ringEquivOfRingEquiv K K e I)
      = FractionalIdeal.count K (primeMap e w) I := by
  have hprincipal : ∀ a : R, a ≠ 0 →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (e a))⁻¹)
        = FractionalIdeal.count K (primeMap e w)
            (FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) a)⁻¹) := by
    intro a ha
    have hspan : (Ideal.span {a} : Ideal R) ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact ha
    have key : ((Ideal.span {e a} : Ideal R) : FractionalIdeal R⁰ K)
        = ((Ideal.map (e : R →+* R) (Ideal.span {a}) : Ideal R) : FractionalIdeal R⁰ K) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.count_inv, FractionalIdeal.count_inv,
      ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton,
      key, count_coe_map e (Ideal.span {a}) hspan w]
  by_cases hI : I = 0
  · rw [hI, map_zero, FractionalIdeal.count_zero, FractionalIdeal.count_zero]
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (R₁ := R) (K := K) I
  have hJ : J ≠ 0 := by
    intro hJ0
    apply hI
    rw [hIJ, hJ0]
    simp
  have hea : e a ≠ 0 := fun h => ha (e.injective (by rw [h, map_zero]))
  have hA : (algebraMap R K) (e a) ≠ 0 := fun h =>
    hea (IsLocalization.injective K (le_refl R⁰) (h.trans (map_zero _).symm))
  have hB : (algebraMap R K) a ≠ 0 := fun h =>
    ha (IsLocalization.injective K (le_refl R⁰) (h.trans (map_zero _).symm))
  have hsa : FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (e a))⁻¹ ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hA)
  have hJmap : Ideal.map (e : R →+* R) J ≠ ⊥ := fun h =>
    hJ ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)
  have hcoe : ((Ideal.map (e : R →+* R) J : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJmap
  have hsa' : FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) a)⁻¹ ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hB)
  have hcoeJ : (J : FractionalIdeal R⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hJ)
  have hsm : FractionalIdeal.ringEquivOfRingEquiv K K e
        (FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J)
      = FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (e a))⁻¹ *
        ((Ideal.map (e : R →+* R) J : Ideal R) : FractionalIdeal R⁰ K) := by
    rw [map_mul, FractionalIdeal.ringEquivOfRingEquiv_spanSingleton]
    rw [show (FractionalIdeal.ringEquivOfRingEquiv K K e) (J : FractionalIdeal R⁰ K)
        = ((Ideal.map (e : R →+* R) J : Ideal R) : FractionalIdeal R⁰ K) from
      Work.CFTLib.ClassGroupTransport.ringEquivOfRingEquiv_coeIdeal (K := K) (L := K)
        (f := e) (I := J)]
    rw [map_inv₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rw [hIJ, hsm,
    show FractionalIdeal.count K w (FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (e a))⁻¹ *
        ((Ideal.map (e : R →+* R) J : Ideal R) : FractionalIdeal R⁰ K))
      = FractionalIdeal.count K w (FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (e a))⁻¹)
        + FractionalIdeal.count K w (((Ideal.map (e : R →+* R) J : Ideal R) : FractionalIdeal R⁰ K))
      from FractionalIdeal.count_mul K w hsa hcoe,
    show FractionalIdeal.count K (primeMap e w)
        (FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * (J : FractionalIdeal R⁰ K))
      = FractionalIdeal.count K (primeMap e w)
          (FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) a)⁻¹)
        + FractionalIdeal.count K (primeMap e w) (J : FractionalIdeal R⁰ K)
      from FractionalIdeal.count_mul K (primeMap e w) hsa' hcoeJ,
    count_coe_map e J hJ w, hprincipal a ha]

end Work.CFTLib.IdealClassMapAux

namespace NK.GlobalCFT.Place

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The inverse of the ring of integers automorphism attached to `σ` is the one attached to
`σ⁻¹`. -/
theorem ringOfIntegersEquiv_symm (σ : L ≃ₐ[K] L) :
    (ringOfIntegersEquiv σ).symm = ringOfIntegersEquiv σ.symm := by
  ext x
  exact (NumberField.RingOfIntegers.mapRingEquiv_symm_apply (σ : L ≃+* L) x).trans
    (NumberField.RingOfIntegers.mapRingEquiv_apply (σ.symm : L ≃+* L) x).symm

end NK.GlobalCFT.Place

namespace Work.CFTLib

variable {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K]

/-- The transported prime of the ring-of-integers automorphism of `σ` is the prime action of
`σ⁻¹`. -/
theorem primeMap_ringOfIntegersEquiv [Algebra F K] (σ : K ≃ₐ[F] K)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    primeMap (NK.GlobalCFT.Place.ringOfIntegersEquiv σ) q
      = NK.GlobalCFT.Place.smulHeightOneSpectrum σ⁻¹ q := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [primeMap_asIdeal_map, NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal,
    NK.GlobalCFT.Place.ringOfIntegersEquiv_symm]
  rfl

end Work.CFTLib

namespace NK.GlobalCFT

namespace Idele

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-! ## The valuation on the adic completion is invariant under the Galois action -/

/-- The `Valued` structure of the adic completion is that of the underlying uniform completion:
`ofCompletion` preserves the valuation. -/
theorem valued_adicCompletion_ofCompletion (q : HeightOneSpectrum (𝓞 K))
    (z : (q.valuation K).Completion) :
    Valued.v (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion z
      : q.adicCompletion K) = Valued.v z :=
  rfl

/-- The isomorphism `q.adicCompletion K ≃+* (q.valuation K).Completion` preserves the
valuations. -/
theorem valued_adicCompletion_equiv (q : HeightOneSpectrum (𝓞 K)) (x : q.adicCompletion K) :
    Valued.v ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K q) x
      : (q.valuation K).Completion) = Valued.v x :=
  rfl

/-- The inverse of the isomorphism `q.adicCompletion K ≃+* (q.valuation K).Completion` preserves
the valuations. -/
theorem valued_adicCompletion_equiv_symm (q : HeightOneSpectrum (𝓞 K))
    (z : (q.valuation K).Completion) :
    Valued.v ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K q).symm z
      : q.adicCompletion K) = Valued.v z :=
  rfl

set_option maxHeartbeats 4000000 in
/-- **The local isomorphism induced by `σ : Gal(K/F)` is an isometry**: the ring isomorphism
`globalCFT_adicCongrEquiv σ q : K_q ≃+* K_{σ q}` of `q`-adic completions preserves the `Valued`
valuations. -/
theorem valued_adicCongrEquiv (σ : K ≃ₐ[F] K) (q : HeightOneSpectrum (𝓞 K))
    (x : q.adicCompletion K) :
    Valued.v ((Galois.globalCFT_adicCongrEquiv σ q) x) = Valued.v x := by
  have hv : Function.Surjective
      (Valued.v : WithVal (q.valuation K) → WithZero (Multiplicative ℤ)) := fun γ => by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.valuation_surjective K q γ
    exact ⟨WithVal.toVal (q.valuation K) r,
      by rw [show Valued.v (WithVal.toVal (q.valuation K) r) = q.valuation K r from rfl]; exact hr⟩
  have hw : Function.Surjective (Valued.v : WithVal
      ((Place.smulHeightOneSpectrum σ q).valuation K) → WithZero (Multiplicative ℤ)) := fun γ => by
    obtain ⟨r, hr⟩ :=
      HeightOneSpectrum.valuation_surjective K (Place.smulHeightOneSpectrum σ q) γ
    exact ⟨WithVal.toVal ((Place.smulHeightOneSpectrum σ q).valuation K) r,
      by rw [show Valued.v (WithVal.toVal ((Place.smulHeightOneSpectrum σ q).valuation K) r)
          = (Place.smulHeightOneSpectrum σ q).valuation K r from rfl]; exact hr⟩
  have hFval : ∀ y : WithVal (q.valuation K),
      Valued.v ((WithVal.congr (q.valuation K)
        ((Place.smulHeightOneSpectrum σ q).valuation K) σ.toRingEquiv) y) = Valued.v y := by
    intro y
    rw [show ((WithVal.congr (q.valuation K) ((Place.smulHeightOneSpectrum σ q).valuation K)
        σ.toRingEquiv) y) = WithVal.toVal _ (σ.toRingEquiv y.ofVal) from
      WithVal.congr_apply (q.valuation K) _ σ.toRingEquiv y]
    rw [show Valued.v (WithVal.toVal ((Place.smulHeightOneSpectrum σ q).valuation K)
          (σ.toRingEquiv y.ofVal))
        = (Place.smulHeightOneSpectrum σ q).valuation K (σ.toRingEquiv y.ofVal) from rfl]
    rw [show Valued.v y = q.valuation K y.ofVal from WithVal.valuation_apply_eq_ofVal (q.valuation K) y]
    exact Galois.globalCFT_valuation_smulHeightOneSpectrum σ q y.ofVal
  have hmain := Work.CFTLib.valued_mapRingEquiv_completion (q.valuation K)
    ((Place.smulHeightOneSpectrum σ q).valuation K)
    (WithVal.congr (q.valuation K) ((Place.smulHeightOneSpectrum σ q).valuation K) σ.toRingEquiv)
    hFval hv hw
    (Galois.globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum σ q).continuous
    (Galois.globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum_symm σ q).continuous
  rw [Galois.globalCFT_adicCongrEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply]
  rw [show Galois.globalCFT_withValCongrEquiv σ q
      = UniformSpace.Completion.mapRingEquiv
          (WithVal.congr (q.valuation K)
            ((Place.smulHeightOneSpectrum σ q).valuation K) σ.toRingEquiv)
          (Galois.globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum σ q).continuous
          (Galois.globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum_symm σ q).continuous
      from rfl]
  rw [valued_adicCompletion_equiv_symm (K := K) (Place.smulHeightOneSpectrum σ q) _,
    hmain (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K q x),
    valued_adicCompletion_equiv (K := K) q x]

/-- The local isomorphism induced by `σ` preserves the valuations, in the inverse direction. -/
theorem valued_adicCongrEquiv_symm (σ : K ≃ₐ[F] K) (q : HeightOneSpectrum (𝓞 K))
    (y : (Place.smulHeightOneSpectrum σ q).adicCompletion K) :
    Valued.v ((Galois.globalCFT_adicCongrEquiv σ q).symm y) = Valued.v y := by
  have h := valued_adicCongrEquiv σ q ((Galois.globalCFT_adicCongrEquiv σ q).symm y)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- The local field isomorphism `K_q ≃+* K_{σ q}` attached to `σ` preserves the local
valuations, in the inverse direction. -/
theorem valued_localRingEquiv_symm (σ : K ≃ₐ[F] K) (q : HeightOneSpectrum (𝓞 K))
    (y : (Place.smulHeightOneSpectrum σ q).adicCompletion K) :
    Valued.v ((Place.localRingEquiv σ (Place.ofFinite q)).symm y) = Valued.v y :=
  valued_adicCongrEquiv_symm σ q y

/-- The local field isomorphism attached to `σ : Gal(K/F)` is the `adicCongrEquiv` of `σ`. -/
theorem localRingEquiv_eq_adicCongrEquiv (σ : K ≃ₐ[F] K) (q : HeightOneSpectrum (𝓞 K)) :
    Place.localRingEquiv σ (Place.ofFinite q) = Galois.globalCFT_adicCongrEquiv σ q := rfl

/-! ## The action of `Gal(K/F)` on the idèle and ideal exponents -/

/-- **The Galois action on idèles moves the `q`-adic exponents**: the exponent of `σ · x` at the
place `σ q` is the exponent of `x` at `q`.  Equivalently, the exponent of `σ · x` at `q` is the
exponent of `x` at `σ⁻¹ q`. -/
theorem exp_smul (σ : K ≃ₐ[F] K) (x : Idele K) (q : HeightOneSpectrum (𝓞 K)) :
    exp q (σ • x) = exp (Place.smulHeightOneSpectrum σ⁻¹ q) x := by
  rw [exp_def, exp_def]
  congr 1
  congr 1
  rw [smul_apply]
  exact valued_localRingEquiv_symm σ⁻¹ q (x (Place.ofFinite (Place.smulHeightOneSpectrum σ⁻¹ q)))

/-- **The Galois action on idèles transports the attached fractional ideal.**  The fractional
ideal of the translate `σ · x` is the image of the fractional ideal of `x` under the ring
automorphism of `𝓞 K` induced by `σ`. -/
theorem idealOf_smul (σ : K ≃ₐ[F] K) (x : Idele K) :
    idealOf (σ • x) = FractionalIdeal.ringEquivOfRingEquiv K K
      (Place.ringOfIntegersEquiv σ) (idealOf x) := by
  have hne : FractionalIdeal.ringEquivOfRingEquiv K K
      (Place.ringOfIntegersEquiv σ) (idealOf x) ≠ 0 := fun h =>
    idealOf_ne_zero x ((FractionalIdeal.ringEquivOfRingEquiv K K
      (Place.ringOfIntegersEquiv σ)).injective (by rw [h, map_zero]))
  refine NK.GlobalCFT.IdeleClassGroup.fractionalIdeal_eq_of_count_eq (idealOf_ne_zero _) hne ?_
  intro w
  rw [show FractionalIdeal.count K w (idealOf (σ • x)) = exp w (σ • x) from count_idealOf _ _]
  rw [show FractionalIdeal.count K w (FractionalIdeal.ringEquivOfRingEquiv K K
        (Place.ringOfIntegersEquiv σ) (idealOf x))
      = FractionalIdeal.count K (Work.CFTLib.primeMap (Place.ringOfIntegersEquiv σ) w) (idealOf x)
      from Work.CFTLib.IdealClassMapAux.count_ringEquivOfRingEquiv _ _ _]
  rw [show FractionalIdeal.count K (Work.CFTLib.primeMap (Place.ringOfIntegersEquiv σ) w) (idealOf x)
      = exp (Work.CFTLib.primeMap (Place.ringOfIntegersEquiv σ) w) x from count_idealOf _ _]
  rw [exp_smul σ x w, Work.CFTLib.primeMap_ringOfIntegersEquiv σ w]

end Idele

end NK.GlobalCFT

namespace Work.CFTLib.IdealClassMapAux

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The transport of ideal classes along a ring equivalence.**  The transport of the class of a
fractional ideal along `e : R ≃+* R` is the class of the transported fractional ideal.

Both sides are group homomorphisms in the fractional ideal which agree on the two families of
generators (principal ideals and integral ideals), and every invertible fractional ideal is the
product of its inverse numerator and an integral ideal. -/
theorem mulEquiv_mk (e : R ≃+* R) (I : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.mulEquiv e (ClassGroup.mk K I) =
      ClassGroup.mk K (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K e :
        FractionalIdeal R⁰ K ≃* FractionalIdeal R⁰ K) I) := by
  let eF : (FractionalIdeal R⁰ K)ˣ ≃* (FractionalIdeal R⁰ K)ˣ :=
    Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K e :
      FractionalIdeal R⁰ K ≃* FractionalIdeal R⁰ K)
  have hmk1 : ∀ x : Kˣ, ClassGroup.mk K (toPrincipalIdeal R K x) = 1 := fun x => by
    rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨(x : K), rfl⟩
  have hmap1 (x : Kˣ) : ClassGroup.mk K (eF (toPrincipalIdeal R K x)) = 1 := by
    have hx : ((x : K)) ≠ 0 := Units.ne_zero x
    have hne : (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) e) (x : K) ≠ 0 :=
      fun h => hx ((IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) e).injective
        (by rw [h, map_zero]))
    have hcoe : eF (toPrincipalIdeal R K x)
        = toPrincipalIdeal R K
            (Units.mk0 ((IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) e) (x : K))
              hne) := by
      apply Units.ext
      show (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K e :
          FractionalIdeal R⁰ K ≃* FractionalIdeal R⁰ K) (toPrincipalIdeal R K x)
          : FractionalIdeal R⁰ K)
        = (toPrincipalIdeal R K (Units.mk0 _ hne) : FractionalIdeal R⁰ K)
      simp only [Units.coe_mapEquiv, coe_toPrincipalIdeal, Units.val_mk0]
      exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton (R := R) (S := R) (K := K) (L := K)
        e (x : K)
    rw [hcoe]
    exact hmk1 _
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (R₁ := R) (K := K) I.val
  have hA : (algebraMap R K) a ≠ 0 := fun h =>
    ha (IsLocalization.injective K (le_refl R⁰) (h.trans (map_zero _).symm))
  have hJ : J ≠ 0 := by
    intro hJ0
    have : I.val = 0 := by rw [hIJ, hJ0]; simp
    exact I.ne_zero this
  have hJmap : Ideal.map (e : R →+* R) J ≠ ⊥ := fun h =>
    hJ ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)
  obtain ⟨J0, hJ0eq⟩ : ∃ J0 : (Ideal R)⁰, (J0 : Ideal R) = J :=
    ⟨⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩, rfl⟩
  obtain ⟨u, hueq⟩ : ∃ u : Kˣ, (u : K) = (algebraMap R K) a :=
    ⟨Units.mk0 _ hA, Units.val_mk0 hA⟩
  have hI' : I * toPrincipalIdeal R K u = FractionalIdeal.mk0 K J0 := by
    apply Units.ext
    rw [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, hIJ, hueq, hJ0eq, mul_assoc,
      mul_comm (↑J) (FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) a)), ← mul_assoc,
      FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hA,
      FractionalIdeal.spanSingleton_one, one_mul]
  have hI : I = (toPrincipalIdeal R K u)⁻¹ * FractionalIdeal.mk0 K J0 := by
    rw [← hI', mul_comm I (toPrincipalIdeal R K u), inv_mul_cancel_left]
  have hP : ClassGroup.mulEquiv e (ClassGroup.mk K (toPrincipalIdeal R K u)⁻¹) = 1 := by
    rw [map_inv (ClassGroup.mk K), hmk1 u, inv_one, map_one]
  have hP' : ClassGroup.mk K (eF (toPrincipalIdeal R K u)⁻¹) = 1 := by
    rw [map_inv eF, map_inv (ClassGroup.mk K), hmap1 u, inv_one]
  have hQ : ClassGroup.mulEquiv e (ClassGroup.mk K (FractionalIdeal.mk0 K J0))
      = ClassGroup.mk K (eF (FractionalIdeal.mk0 K J0)) := by
    rw [ClassGroup.mk_mk0, Work.CFTLib.ClassGroupTransport.mk0_mulEquiv]
    rw [show eF (FractionalIdeal.mk0 K J0)
        = FractionalIdeal.mk0 K ⟨Ideal.map (e : R →+* R) (J0 : Ideal R),
            mem_nonZeroDivisors_of_ne_zero (fun h => by rw [hJ0eq] at h; exact hJmap h)⟩ from
      Units.ext (by
        rw [Units.coe_mapEquiv, FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0]
        exact Work.CFTLib.ClassGroupTransport.ringEquivOfRingEquiv_coeIdeal (K := K) (L := K)
          (f := e) (I := (J0 : Ideal R)))]
    rw [ClassGroup.mk_mk0]
  rw [hI, map_mul (ClassGroup.mk K), map_mul (ClassGroup.mulEquiv e), map_mul eF,
    map_mul (ClassGroup.mk K), hP, hP', hQ]

end Work.CFTLib.IdealClassMapAux

namespace Work.CFTLib

open NK.GlobalCFT

/-- **The ideal class map commutes with the Galois action on idèles.**  For `σ : Gal(K/F)` and an
idèle `x` of `K`, the ideal class of the translate `σ · x` is the transport of the ideal class of
`x` along the automorphism of `Cl(𝓞 K)` induced by `σ`. -/
theorem idealClassMap_smul {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (σ : K ≃ₐ[F] K) (x : NK.GlobalCFT.Idele K) :
    NK.GlobalCFT.IdeleClassGroup.idealClassMap K (σ • x) =
      Work.CFTLib.clEquiv F K σ (NK.GlobalCFT.IdeleClassGroup.idealClassMap K x) := by
  have hne : FractionalIdeal.ringEquivOfRingEquiv K K
      (NK.GlobalCFT.Place.ringOfIntegersEquiv σ) (NK.GlobalCFT.Idele.idealOf x) ≠ 0 := fun h =>
    NK.GlobalCFT.Idele.idealOf_ne_zero x ((FractionalIdeal.ringEquivOfRingEquiv K K
      (NK.GlobalCFT.Place.ringOfIntegersEquiv σ)).injective (by rw [h, map_zero]))
  have hmk : (Units.mk0 (NK.GlobalCFT.Idele.idealOf (σ • x))
        (NK.GlobalCFT.Idele.idealOf_ne_zero (σ • x)))
      = Units.mk0 (FractionalIdeal.ringEquivOfRingEquiv K K
          (NK.GlobalCFT.Place.ringOfIntegersEquiv σ) (NK.GlobalCFT.Idele.idealOf x)) hne :=
    Units.ext (by rw [Units.val_mk0, Units.val_mk0, NK.GlobalCFT.Idele.idealOf_smul])
  rw [NK.GlobalCFT.IdeleClassGroup.idealClassMap_apply,
    NK.GlobalCFT.IdeleClassGroup.idealClassMap_apply, hmk]
  rw [show Work.CFTLib.clEquiv F K σ
      = ClassGroup.mulEquiv (NK.GlobalCFT.Place.ringOfIntegersEquiv σ) from rfl]
  rw [Work.CFTLib.IdealClassMapAux.mulEquiv_mk]
  congr 1
  exact Units.ext (by
    rw [Units.coe_mapEquiv, Units.val_mk0, Units.val_mk0]
    rfl)

end Work.CFTLib
