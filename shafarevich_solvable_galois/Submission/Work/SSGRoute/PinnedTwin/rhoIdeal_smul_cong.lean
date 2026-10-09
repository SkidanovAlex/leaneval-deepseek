import Mathlib
import Submission.Work.SSGRoute.PinnedTwin.Shim
import Submission.Work.SSGRoute.PinnedTwin.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PinnedTwin

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

/-!
### The congruence `ρ • 𝔦(I) ≡ 𝔦(ρ I) (mod 𝔪)` for an ideal coprime to the modulus

This is the version of `PinnedTwin.ideleOfIdeal_smul_cong` for an *arbitrary* nonzero ideal `I`
(instead of a single prime), under the hypothesis `hc` that no prime dividing `I` occurs in the
support of the modulus `𝔪`.

The proof is the pointwise computation at the finite places, with the single new ingredient being
the transport of the `q`-adic count through the conjugation of ideals
(`count_rhoIdeal`, proved below from the factorization theory of ideals in a Dedekind domain).
-/

/-- The idèle `1` is congruent to `1` modulo every level. -/
private lemma isCongAt_one {K : Type} [Field K] [NumberField K]
    (m : HeightOneSpectrum (𝓞 K) → ℕ) (q : HeightOneSpectrum (𝓞 K)) :
    NK.NUV2.RouteB.IsCongAt K m q (1 : (q.adicCompletion K)ˣ) := by
  rw [NK.NUV2.RouteB.IsCongAt]
  have hzero : Valued.v (((1 : (q.adicCompletion K)ˣ) : q.adicCompletion K) - 1) = 0 := by simp
  rw [hzero]
  exact zero_le

/-- A local *unit* at the finite place `q` is congruent to `1` modulo the level `0`. -/
private lemma isCongAt_of_valued_eq_one {K : Type} [Field K] [NumberField K]
    (m : HeightOneSpectrum (𝓞 K) → ℕ) (q : HeightOneSpectrum (𝓞 K)) (hmq : m q = 0)
    (z : (q.adicCompletion K)ˣ) (hz : Valued.v (z : q.adicCompletion K) = 1) :
    NK.NUV2.RouteB.IsCongAt K m q z := by
  rw [NK.NUV2.RouteB.IsCongAt, hmq]
  have hzint : (z : q.adicCompletion K) ∈ q.adicCompletionIntegers K := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K q]
    exact le_of_eq hz
  have hsub : (z : q.adicCompletion K) - 1 ∈ q.adicCompletionIntegers K :=
    sub_mem hzint (one_mem _)
  have h := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K q).mp hsub
  simpa using h

/-! ### The transport of the `q`-adic count through conjugation of ideals -/

/-- **The `q`-adic count of a conjugate ideal.**  For a ring automorphism `e` of `𝓞 K` and a
nonzero ideal `I`, the exponent of the place `e q` in `I.map e` is the exponent of `q` in `I`.

This is the ideal-theoretic content of the Galois equivariance of the divisor of an element. -/
private lemma count_mapRingEquiv {K : Type} [Field K] [NumberField K]
    (e : 𝓞 K ≃+* 𝓞 K) (I : Ideal (𝓞 K)) (hI : I ≠ 0) (q : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K
        (Commons.NumberTheory.NumberField.Completion.HeightOneSpectrum.mapRingEquiv e q)
        (((I.map (e : 𝓞 K →+* 𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.count K q (I : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  have hf_inj : Function.Injective (e : 𝓞 K →+* 𝓞 K) := e.injective
  have hf_surj : Function.Surjective (e : 𝓞 K →+* 𝓞 K) := e.surjective
  set m : ℕ := Multiset.count q.asIdeal
    (UniqueFactorizationMonoid.normalizedFactors I) with hm
  have hcountA : (Associates.mk q.asIdeal).count (Associates.mk I).factors = m := by
    rw [Ideal.count_associates_factors_eq hI q.isPrime q.ne_bot]
  have hIA : (Associates.mk I : Associates (Ideal (𝓞 K))) ≠ 0 := by
    rw [Associates.mk_ne_zero]; exact hI
  have hIrr : Irreducible (Associates.mk q.asIdeal : Associates (Ideal (𝓞 K))) := by
    rw [Associates.irreducible_mk]; exact q.irreducible
  have hdvdA : ∀ k : ℕ, (q.asIdeal ^ k ∣ I) ↔ k ≤ m := by
    intro k
    rw [← Associates.mk_dvd_mk, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le hIA hIrr).trans (by rw [hcountA])
  have hmap0 : I.map (e : 𝓞 K →+* 𝓞 K) ≠ 0 := by
    intro h
    exact hI ((Ideal.map_eq_bot_iff_of_injective (f := (e : 𝓞 K →+* 𝓞 K)) hf_inj).mp h)
  have hqmap0 : q.asIdeal.map (e : 𝓞 K →+* 𝓞 K) ≠ 0 := by
    intro h
    exact q.ne_bot ((Ideal.map_eq_bot_iff_of_injective (f := (e : 𝓞 K →+* 𝓞 K)) hf_inj).mp h)
  have hqmapPrime : (q.asIdeal.map (e : 𝓞 K →+* 𝓞 K)).IsPrime := by
    haveI := q.isPrime
    exact Ideal.map_isPrime_of_equiv (e : 𝓞 K ≃+* 𝓞 K)
  have hmapdvd : ∀ k : ℕ,
      ((q.asIdeal.map (e : 𝓞 K →+* 𝓞 K)) ^ k ∣ I.map (e : 𝓞 K →+* 𝓞 K)) ↔ k ≤ m := by
    intro k
    rw [← hdvdA k, Ideal.dvd_iff_le, Ideal.dvd_iff_le, ← Ideal.map_pow]
    constructor
    · intro h
      have h2 := Ideal.comap_mono (f := (e : 𝓞 K →+* 𝓞 K)) h
      rwa [Ideal.comap_map_of_surjective (e : 𝓞 K →+* 𝓞 K) hf_surj I,
        Ideal.comap_map_of_surjective (e : 𝓞 K →+* 𝓞 K) hf_surj (q.asIdeal ^ k),
        Ideal.comap_bot_of_injective (e : 𝓞 K →+* 𝓞 K) hf_inj, sup_bot_eq,
        sup_bot_eq] at h2
    · intro h; exact Ideal.map_mono h
  have hIA' : (Associates.mk (I.map (e : 𝓞 K →+* 𝓞 K)) : Associates (Ideal (𝓞 K))) ≠ 0 := by
    rw [Associates.mk_ne_zero]; exact hmap0
  have hIrr' : Irreducible (Associates.mk (q.asIdeal.map (e : 𝓞 K →+* 𝓞 K)) :
      Associates (Ideal (𝓞 K))) := by
    rw [Associates.irreducible_mk]
    exact (Ideal.prime_of_isPrime hqmap0 hqmapPrime).irreducible
  have hcountBm : (Associates.mk (q.asIdeal.map (e : 𝓞 K →+* 𝓞 K))).count
      (Associates.mk (I.map (e : 𝓞 K →+* 𝓞 K))).factors = m := by
    have key : ∀ k : ℕ,
        k ≤ (Associates.mk (q.asIdeal.map (e : 𝓞 K →+* 𝓞 K))).count
              (Associates.mk (I.map (e : 𝓞 K →+* 𝓞 K))).factors ↔ k ≤ m := by
      intro k
      rw [← hmapdvd k, ← Associates.mk_dvd_mk, Associates.mk_pow]
      exact (Associates.prime_pow_dvd_iff_le hIA' hIrr').symm
    exact le_antisymm ((key _).mp le_rfl) ((key m).mpr le_rfl)
  have hcountB : FractionalIdeal.count K
      (Commons.NumberTheory.NumberField.Completion.HeightOneSpectrum.mapRingEquiv e q)
      (((I.map (e : 𝓞 K →+* 𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = (m : ℤ) := by
    rw [FractionalIdeal.count_coe K
        (Commons.NumberTheory.NumberField.Completion.HeightOneSpectrum.mapRingEquiv e q) hmap0,
      Commons.NumberTheory.NumberField.Completion.HeightOneSpectrum.mapRingEquiv_asIdeal,
      hcountBm]
  rw [hcountB, FractionalIdeal.count_coe K q hI, hcountA]

/-- **The `q`-adic count of a `ρ`-conjugate ideal**, in the form used below. -/
private lemma count_rhoIdeal {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K q (rhoIdeal ρ I : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.count K
          (Commons.NumberTheory.NumberField.Completion.placeSmul ρ⁻¹ q)
          (I : FractionalIdeal (𝓞 K)⁰ K) := by
  have hfix : Commons.NumberTheory.NumberField.Completion.HeightOneSpectrum.mapRingEquiv
      (rhoRing ρ) (Commons.NumberTheory.NumberField.Completion.placeSmul ρ⁻¹ q) = q := by
    change Commons.NumberTheory.NumberField.Completion.placeSmul ρ
      (Commons.NumberTheory.NumberField.Completion.placeSmul ρ⁻¹ q) = q
    rw [← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, mul_inv_cancel,
      Commons.NumberTheory.NumberField.Completion.placeSmul_one]
  have h := count_mapRingEquiv (rhoRing ρ) I hI
    (Commons.NumberTheory.NumberField.Completion.placeSmul ρ⁻¹ q)
  rwa [hfix] at h

/-! ### The idèle of a `ρ`-conjugated ideal -/

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

/-- **The value of `ρ • 𝔦(I)` at a finite place**, in terms of the local uniformizer at the
preimage place. -/
private lemma smul_ideleOfIdeal_ofFinite (ρ : K ≃ₐ[k] K) (I : Ideal (𝓞 K))
    (q : HeightOneSpectrum (𝓞 K)) :
    (ρ • NK.HeckeL.ideleOfIdeal K I) (NK.GlobalCFT.Place.ofFinite q)
      = Units.map (NK.GlobalCFT.Place.localRingEquiv ρ⁻¹ (NK.GlobalCFT.Place.ofFinite q)).symm.toMonoidHom
          (NK.GlobalCFT.IdeleClassGroup.unifUnit K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
            ^ (FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
                (I : FractionalIdeal (𝓞 K)⁰ K))) := by
  rw [NK.GlobalCFT.Idele.smul_apply]; rfl

/-- The canonical local isomorphism is an isometry for `Valued.v`. -/
private lemma valued_symm_adicCongr (ρ : K ≃ₐ[k] K) (q : HeightOneSpectrum (𝓞 K))
    (y : (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q).adicCompletion K) :
    Valued.v ((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv ρ⁻¹ q).symm y) = Valued.v y := by
  have h := NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_valued ρ⁻¹ q
    ((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv ρ⁻¹ q).symm y)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- **The `q`-adic valuation of `ρ • 𝔦(I)`.** -/
private lemma valued_smul_ideleOfIdeal (ρ : K ≃ₐ[k] K) (I : Ideal (𝓞 K))
    (q : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((ρ • NK.HeckeL.ideleOfIdeal K I) (NK.GlobalCFT.Place.ofFinite q)) :
        q.adicCompletion K)
      = WithZero.exp (-(FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
          (I : FractionalIdeal (𝓞 K)⁰ K))) := by
  rw [smul_ideleOfIdeal_ofFinite, Units.coe_map]
  refine (Eq.trans ?_ (NK.GlobalCFT.IdeleClassGroup.valued_unifUnit_zpow
    (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
    (FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
      (I : FractionalIdeal (𝓞 K)⁰ K))))
  exact valued_symm_adicCongr ρ q _

theorem rhoIdeal_smul_cong {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (𝔪 : NK.NUV2.RouteB.Modulus K) (hpos : 𝔪.pos = ∅)
    (hstab : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q)
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0)
    (hc : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ I) :
    (ρ • NK.HeckeL.ideleOfIdeal K I) *
      (NK.HeckeL.ideleOfIdeal K (Work.SSGRoute.PinnedTwin.rhoIdeal ρ I))⁻¹
      ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  classical
  rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff]
  refine ⟨fun q => ?_, fun w _ hmem => by simp [hpos] at hmem⟩
  -- the count identity at the place `q`
  have hcnt : FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
        (I : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.count K q (rhoIdeal ρ I : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum ρ⁻¹ q]
    exact (count_rhoIdeal ρ I hI q).symm
  have hv1 : Valued.v (((ρ • NK.HeckeL.ideleOfIdeal K I)
        (NK.GlobalCFT.Place.ofFinite q)) : q.adicCompletion K)
      = WithZero.exp (-(FractionalIdeal.count K q (rhoIdeal ρ I : FractionalIdeal (𝓞 K)⁰ K))) := by
    rw [valued_smul_ideleOfIdeal, hcnt]
  have hv2 : Valued.v (((NK.HeckeL.ideleOfIdeal K (rhoIdeal ρ I))
        (NK.GlobalCFT.Place.ofFinite q)) : q.adicCompletion K)
      = WithZero.exp (-(FractionalIdeal.count K q (rhoIdeal ρ I : FractionalIdeal (𝓞 K)⁰ K))) := by
    change Valued.v (((NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^
      (FractionalIdeal.count K q (rhoIdeal ρ I : FractionalIdeal (𝓞 K)⁰ K)) :
        (q.adicCompletion K)ˣ) : q.adicCompletion K)) = _
    rw [NK.GlobalCFT.IdeleClassGroup.valued_unifUnit_zpow]
  have hv : Valued.v ((((ρ • NK.HeckeL.ideleOfIdeal K I) *
        (NK.HeckeL.ideleOfIdeal K (rhoIdeal ρ I))⁻¹)
        (NK.GlobalCFT.Place.ofFinite q)) : q.adicCompletion K) = 1 := by
    rw [NK.GlobalCFT.Idele.mul_apply, Units.val_mul, map_mul, NK.GlobalCFT.Idele.inv_apply,
      Units.val_inv_eq_inv_val, map_inv₀, hv1, hv2]
    exact mul_inv_cancel₀ (by simp)
  by_cases hq : FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
      (I : FractionalIdeal (𝓞 K)⁰ K) = 0
  · -- both factors are trivial at `q`
    have h1 : (ρ • NK.HeckeL.ideleOfIdeal K I) (NK.GlobalCFT.Place.ofFinite q) = 1 := by
      rw [smul_ideleOfIdeal_ofFinite, hq, zpow_zero, map_one]
    have h2 : (NK.HeckeL.ideleOfIdeal K (rhoIdeal ρ I)) (NK.GlobalCFT.Place.ofFinite q) = 1 := by
      change NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^
        (FractionalIdeal.count K q (rhoIdeal ρ I : FractionalIdeal (𝓞 K)⁰ K)) = 1
      rw [← hcnt, hq, zpow_zero]
    have hxq : ((ρ • NK.HeckeL.ideleOfIdeal K I) *
        (NK.HeckeL.ideleOfIdeal K (rhoIdeal ρ I))⁻¹)
        (NK.GlobalCFT.Place.ofFinite q) = 1 := by
      rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, h1, h2, one_mul, inv_one]
    exact ⟨by rw [hxq, Units.val_one, map_one], by rw [hxq]; exact isCongAt_one (𝔪.exps) q⟩
  · -- the ratio is a local unit, and `𝔪` is trivial at `q`
    have hdvd : (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q).asIdeal ∣ I := by
      have h := hq
      rw [FractionalIdeal.count_coe K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q) hI] at h
      have hnat : (Associates.mk (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q).asIdeal).count
          (Associates.mk I).factors ≠ 0 := by
        intro hh
        exact h (by rw [hh]; rfl)
      exact (Associates.count_ne_zero_iff_dvd hI
        (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q).irreducible).mp hnat
    have hexp1 : 𝔪.exps (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q) = 0 := by
      by_contra h
      exact ((hc (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)) h) hdvd
    have hfix' : Commons.NumberTheory.NumberField.Completion.placeSmul ρ
        (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q) = q := by
      rw [← NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum ρ⁻¹ q,
        ← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, mul_inv_cancel,
        Commons.NumberTheory.NumberField.Completion.placeSmul_one]
    have hexp : 𝔪.exps q = 0 := by
      have h := hstab (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
      rw [hfix', hexp1] at h
      exact h
    exact ⟨hv, isCongAt_of_valued_eq_one (𝔪.exps) q hexp _ hv⟩

end Work.SSGRoute.PinnedTwin
