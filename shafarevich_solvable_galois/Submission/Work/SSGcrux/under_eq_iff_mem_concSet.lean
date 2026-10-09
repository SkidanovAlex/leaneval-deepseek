import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGcrux.galRes_mem_concSet_iff
import Submission.Work.SSGcrux.under_smul_eq_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

/-- **The detecting place of `K₁L` and its `concSet` bookkeeping.** -/
theorem under_eq_iff_mem_concSet
  {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional k K]
    [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
  (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
  (K1 : IntermediateField k K) [FiniteDimensional k K1] [IsGalois k K1]
  (K1L : IntermediateField k L) [FiniteDimensional k K1L]
  (eK1 : ↥K1 ≃ₐ[k] ↥K1L) (heK1 : ∀ x : ↥K1, (eK1 x : L) = algebraMap K L (x : K))
  (hH : N.comap (SSGRoute.PTExt.galRes k K L) = K1L.fixingSubgroup)
  (w : NK.GlobalCFT.Place K)
  (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (hwq : w = NK.GlobalCFT.Place.ofFinite q)
  (γ : K ≃ₐ[k] K)
  (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
  (hq' : q'.asIdeal.LiesOver q.asIdeal)
  (σ₀ : L ≃ₐ[k] L) (hσ₀ : SSGRoute.PTExt.galRes k K L σ₀ = γ) :
  ∃ u₀' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L),
    (u₀'.asIdeal = Ideal.map
        ((NumberField.RingOfIntegers.mapAlgEquiv eK1) : NumberField.RingOfIntegers ↥K1 →+*
          NumberField.RingOfIntegers ↥K1L)
        ((NK.GlobalCFT.Place.smulHeightOneSpectrum γ q).asIdeal.under
          (NumberField.RingOfIntegers ↥K1))) ∧
    (∀ x : L ≃ₐ[k] L,
      ((NK.GlobalCFT.Place.smulHeightOneSpectrum x q').asIdeal.under
          (NumberField.RingOfIntegers ↥K1L) = u₀'.asIdeal) ↔
        SSGRoute.PTExt.galRes k K L x ∈ Work.SSGRoute.TPatom.concSet k K w N γ) := by
  classical
  -- `K₁L` is Galois over `k`, transported from `K₁` along `eK1`
  haveI hgalK1L : IsGalois k ↥K1L := IsGalois.of_algEquiv eK1
  -- the induced ring isomorphism `𝓞 K₁ ≃+* 𝓞 K₁L`
  let eR : NumberField.RingOfIntegers ↥K1 ≃+* NumberField.RingOfIntegers ↥K1L :=
    (NumberField.RingOfIntegers.mapAlgEquiv eK1).toRingEquiv
  have hrfl : (eR : NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L) =
      ((NumberField.RingOfIntegers.mapAlgEquiv eK1) :
        NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L) := rfl
  -- the two composite maps `𝓞 K₁ → 𝓞 L` (through `𝓞 K₁L` and through `𝓞 K`) agree
  have hkey : ∀ y : NumberField.RingOfIntegers ↥K1,
      algebraMap (NumberField.RingOfIntegers ↥K1L) (NumberField.RingOfIntegers L) (eR y)
        = algebraMap (NumberField.RingOfIntegers ↥K1) (NumberField.RingOfIntegers L) y := by
    intro y
    apply NumberField.RingOfIntegers.coe_injective
    rw [← IsScalarTower.algebraMap_apply (R := NumberField.RingOfIntegers ↥K1L)
          (S := NumberField.RingOfIntegers L) (A := L) (eR y),
        ← IsScalarTower.algebraMap_apply (R := NumberField.RingOfIntegers ↥K1)
          (S := NumberField.RingOfIntegers L) (A := L) y]
    change (((eR y : NumberField.RingOfIntegers ↥K1L) : ↥K1L) : L)
      = algebraMap K L (((y : NumberField.RingOfIntegers ↥K1) : ↥K1) : K)
    rw [show ((eR y : NumberField.RingOfIntegers ↥K1L) : ↥K1L) = eK1 (y : ↥K1) from
      NumberField.RingOfIntegers.mapRingHom_apply (f := (eK1 : ↥K1 →+* ↥K1L)) y]
    rw [heK1 (y : ↥K1)]
  -- Step (i): contraction to `𝓞 K₁L` is the `eK1`-image of the contraction to `𝓞 K₁`
  have htrans : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      Ideal.under (NumberField.RingOfIntegers ↥K1L) Q.asIdeal
        = Ideal.map (eR : NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L)
            (Ideal.under (NumberField.RingOfIntegers ↥K1) Q.asIdeal) := by
    intro Q
    have hcomap : Ideal.comap (eR : NumberField.RingOfIntegers ↥K1 →+*
          NumberField.RingOfIntegers ↥K1L)
        (Ideal.under (NumberField.RingOfIntegers ↥K1L) Q.asIdeal)
        = Ideal.under (NumberField.RingOfIntegers ↥K1) Q.asIdeal := by
      rw [show Ideal.under (NumberField.RingOfIntegers ↥K1L) Q.asIdeal
            = Ideal.comap (algebraMap (NumberField.RingOfIntegers ↥K1L)
                (NumberField.RingOfIntegers L)) Q.asIdeal from
          Ideal.under_def (NumberField.RingOfIntegers ↥K1L) Q.asIdeal,
          show Ideal.under (NumberField.RingOfIntegers ↥K1) Q.asIdeal
            = Ideal.comap (algebraMap (NumberField.RingOfIntegers ↥K1)
                (NumberField.RingOfIntegers L)) Q.asIdeal from
          Ideal.under_def (NumberField.RingOfIntegers ↥K1) Q.asIdeal,
          Ideal.comap_comap]
      rw [show (algebraMap (NumberField.RingOfIntegers ↥K1L) (NumberField.RingOfIntegers L)).comp
            (eR : NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L)
          = algebraMap (NumberField.RingOfIntegers ↥K1) (NumberField.RingOfIntegers L) from
        RingHom.ext hkey]
    have hmap : Ideal.map (eR : NumberField.RingOfIntegers ↥K1 →+*
          NumberField.RingOfIntegers ↥K1L)
        (Ideal.comap (eR : NumberField.RingOfIntegers ↥K1 →+*
          NumberField.RingOfIntegers ↥K1L)
          (Ideal.under (NumberField.RingOfIntegers ↥K1L) Q.asIdeal))
        = Ideal.under (NumberField.RingOfIntegers ↥K1L) Q.asIdeal :=
      Ideal.map_comap_eq_self_of_equiv eR _
    rw [hcomap] at hmap
    exact hmap.symm
  -- Step (ii): the contractions of `σ₀ • q'` and `γ • q` to `𝓞 K₁` agree
  have hres : σ₀.restrictNormal K = γ := by
    rw [← hσ₀]
    rfl
  have hmid : Ideal.under (NumberField.RingOfIntegers K)
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ₀ q').asIdeal
      = (NK.GlobalCFT.Place.smulHeightOneSpectrum γ q).asIdeal := by
    rw [Work.SSGRoute.Sha2Lib.under_smul_heightOneSpectrum (k := k) (K := K) (L := L) σ₀ q',
        hq'.over.symm, hres]
    exact (NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal γ q).symm
  have hunder : (NK.GlobalCFT.Place.smulHeightOneSpectrum σ₀ q').asIdeal.under
        (NumberField.RingOfIntegers ↥K1)
      = (NK.GlobalCFT.Place.smulHeightOneSpectrum γ q).asIdeal.under
        (NumberField.RingOfIntegers ↥K1) := by
    rw [← Ideal.under_under (A := NumberField.RingOfIntegers ↥K1)
          (B := NumberField.RingOfIntegers K)
          (NK.GlobalCFT.Place.smulHeightOneSpectrum σ₀ q').asIdeal, hmid]
  -- the detecting place of `K₁L`
  let u₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1) :=
    ⟨(NK.GlobalCFT.Place.smulHeightOneSpectrum γ q).asIdeal.under
        (NumberField.RingOfIntegers ↥K1), inferInstance,
      Ideal.under_ne_bot (NumberField.RingOfIntegers ↥K1)
        (NK.GlobalCFT.Place.smulHeightOneSpectrum γ q).ne_bot⟩
  let u₀' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L) :=
    ⟨Ideal.map (eR : NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L)
        u₀.asIdeal,
      Ideal.isPrime_of_prime (Ideal.map_prime_of_equiv eR u₀.prime u₀.ne_bot),
      fun h => u₀.ne_bot ((Ideal.map_eq_bot_iff_of_injective (f := (eR : NumberField.RingOfIntegers ↥K1 →+*
        NumberField.RingOfIntegers ↥K1L)) eR.injective).mp h)⟩
  have hu₀'asIdeal : u₀'.asIdeal = Ideal.map
      (eR : NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L)
      ((NK.GlobalCFT.Place.smulHeightOneSpectrum γ q).asIdeal.under
        (NumberField.RingOfIntegers ↥K1)) := by
    dsimp only [u₀', u₀]
  have hu₀' : u₀'.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L)
      (NK.GlobalCFT.Place.smulHeightOneSpectrum σ₀ q').asIdeal := by
    calc u₀'.asIdeal
        = Ideal.map (eR : NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L)
            ((NK.GlobalCFT.Place.smulHeightOneSpectrum γ q).asIdeal.under
              (NumberField.RingOfIntegers ↥K1)) := hu₀'asIdeal
      _ = Ideal.map (eR : NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L)
            ((NK.GlobalCFT.Place.smulHeightOneSpectrum σ₀ q').asIdeal.under
              (NumberField.RingOfIntegers ↥K1)) := by rw [← hunder]
      _ = Ideal.under (NumberField.RingOfIntegers ↥K1L)
            (NK.GlobalCFT.Place.smulHeightOneSpectrum σ₀ q').asIdeal :=
          (htrans (NK.GlobalCFT.Place.smulHeightOneSpectrum σ₀ q')).symm
  -- the fixing condition of `K₁L` matches membership in `N.comap galRes`
  have hfix_iff : ∀ h : L ≃ₐ[k] L,
      (∀ y : ↥K1L, h (algebraMap ↥K1L L y) = algebraMap ↥K1L L y) ↔
        h ∈ N.comap (SSGRoute.PTExt.galRes k K L) := by
    intro h
    rw [hH, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hh y hy
      simpa using hh ⟨y, hy⟩
    · intro hh y
      simpa using hh (y : L) y.2
  refine ⟨u₀', ?_, ?_⟩
  · rw [hu₀'asIdeal, hrfl]
  · intro x
    have hstep : (Ideal.under (NumberField.RingOfIntegers ↥K1L)
          (NK.GlobalCFT.Place.smulHeightOneSpectrum x q').asIdeal = u₀'.asIdeal) ↔
        ∃ h ∈ N.comap (SSGRoute.PTExt.galRes k K L),
          ∃ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := L)
            (NK.GlobalCFT.Place.ofFinite q'), x = h * σ₀ * δ := by
      rw [hu₀']
      rw [← smul_primeIdeal_eq_smulHeightOneSpectrum' (k := k) (L := L) x q',
          ← smul_primeIdeal_eq_smulHeightOneSpectrum' (k := k) (L := L) σ₀ q']
      rw [under_smul_eq_iff (k := k) (K := ↥K1L) (L := L) q' x σ₀]
      constructor
      · rintro ⟨h, hfix, δ, hδ, hx⟩
        exact ⟨h, (hfix_iff h).mp hfix, δ, hδ, hx⟩
      · rintro ⟨h, hh, δ, hδ, hx⟩
        exact ⟨h, (hfix_iff h).mpr hh, δ, hδ, hx⟩
    rw [hstep]
    exact (galRes_mem_concSet_iff (k := k) (K := K) (L := L) w q hwq q' hq' N σ₀ x γ hσ₀).symm

end Work.SSGcrux
