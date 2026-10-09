import Mathlib
import Submission.Work.SSGRoute.SSG8Escape.Setup
import Submission.Work.SSGRoute.step4_y_escape_v2.localFactor_productFormula_clean
import Submission.Work.GrunwaldEscapeCore.L1Korth.idele_decomposition_tFreePart
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinSetup
import Submission.Work.SSG8Escape.localField_not_real_of_no_involutions
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.N2v2

open scoped NumberField
open NumberField IsDedekindDomain

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-! ## `↥K` has no real place

The hypothesis `hKimag` of the main theorem says that `Gal(Ω/↥K)` has no element of order two.
For `p = 2` this forces `↥K` to have no real place (a real place produces the complex conjugation as
an involution of `Gal(Ω/↥K)`), and for `p ≠ 2` the primitive `p`-th root of unity `ζ ∈ ↥K` forces
`↥K` to be totally imaginary.  Both halves are available in the workspace: the `p = 2` half as
`Work.SSG8Escape.localField_not_real_of_no_involutions` (whose hypothesis is that the completion at
an infinite place has no real-valued ring homomorphism), and `p ≠ 2`
as `Work.SSGRoute.ZDataMup.isComplex_infinitePlace_of_isPrimitiveRoot`. -/

/-- **`↥K` has no real infinite place**, from `hKimag` (`p = 2`) and a primitive `p`-th root of
unity `ζ ∈ ↥K` (`p ≠ 2`), with `Ω` an algebraic closure of `k` and `K / k` finite. -/
theorem noRealPlace_of_hKimag_zeta
    (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1) :
    ∀ w : NumberField.InfinitePlace ↥K, w.IsComplex := by
  intro w
  by_contra hwc
  have hwR : w.IsReal := NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hwc
  refine Work.SSG8Escape.localField_not_real_of_no_involutions p K ζ hζ hKimag
    (NK.GlobalCFT.Place.ofInfinite w) (NK.GlobalCFT.Place.not_isFinite_ofInfinite w) ?_
  exact ⟨(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hwR).toRingHom, trivial⟩

/-! ## Idèles trivial on `T'` and local units elsewhere are norm idèles

This is `mem_normImage_iff_localNorm_of_finiteDimensional`: an idèle is a norm idèle exactly when
all its local components are local norms.  At a finite prime `𝔭 ∈ T'` the component is `1`; at a
finite prime `𝔮 ∉ T'` it is a local unit, and local units are local norms at unramified primes
(`NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified`, using that `F/↥K` is
unramified outside `T'`); at an infinite place the local norm subgroup is everything because `↥K`
has no real place. -/

theorem mem_normImage_of_localUnits_of_trivialOn
    {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (T' : Finset (NK.Chebotarev.PrimeIdeal K)) (x : NK.GlobalCFT.Idele K)
    (hT' : ∀ 𝔭 ∈ T', x (NK.GlobalCFT.Place.ofFinite 𝔭) = 1)
    (hunr : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := K) (L := F) 𝔮)
    (hunit : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K, 𝔮 ∉ T' →
      x (NK.GlobalCFT.Place.ofFinite 𝔮) ∈
        NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔮))
    (hnoReal : ∀ w : NumberField.InfinitePlace K, w.IsComplex) :
    x ∈ NK.GlobalCFT.Idele.normImage K F := by
  classical
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional]
  intro v
  rcases v with w | 𝔮
  · -- the archimedean places: `↥K` has no real place, so the local norm is onto
    obtain ⟨w', hw'⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := F) w
    haveI : w'.LiesOver w := hw'
    have htop : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := F)
        (NK.GlobalCFT.Place.ofInfinite w) = ⊤ :=
      NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top
        (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex
          (hnoReal w)
          (NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w' (hnoReal w)))
    exact NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup
      (by rw [htop]; exact Subgroup.mem_top _)
  · -- the finite places
    have hmem : x (NK.GlobalCFT.Place.ofFinite 𝔮) ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := F)
          (NK.GlobalCFT.Place.ofFinite 𝔮) := by
      by_cases hq : 𝔮 ∈ T'
      · rw [hT' 𝔮 hq]; exact Subgroup.one_mem _
      · exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified 𝔮 (hunr 𝔮 hq)
          (hunit 𝔮 hq)
    exact NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup hmem

/-- **Artin fixes the symbol of the `T'`-free part of `div a` once the local factors cancel.**
For `p` odd, or `K` without real places (`hKimag`, hence every archimedean local factor is `1`),
an abelian finite Galois `F/↥K` containing the Kummer field of `c`, a character `χ` of `Gal(F/↥K)`
whose pull-back to `G_↥K` is the Kummer character of `c`, an idèlic Artin map `Φ : 𝕀_↥K →* Gal(F/↥K)`
killing the principal idèles and the idèlic norms, and a finite set `T'` of primes of `↥K` outside
which `F/↥K` is unramified: if the product of the `χ`-values of the local factors of `a` over `T'`
is `1`, then `χ (Φ (fracIdele (tFreePart T' a))) = 1`. -/
theorem artin_fixes_of_local_factors
    (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (F : IntermediateField ↥K Ω) [FiniteDimensional ↥K F] [IsGalois ↥K F] [NumberField ↥F]
    [IsMulCommutative (↥F ≃ₐ[↥K] ↥F)]
    (c : (↥K)ˣ) (hc : NK.LocalAnabelian.kummerField (p := p) (K' := Ω) c ≤ F)
    (χ : (↥F ≃ₐ[↥K] ↥F) →* Multiplicative (ZMod p))
    (hχ : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χ (AlgEquiv.restrictNormalHom F σ) =
        Multiplicative.ofAdd (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ))
    (a : (↥K)ˣ) (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hLT : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥F) 𝔮)
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥F ≃ₐ[↥K] ↥F))
    (hΦprin : ∀ x : (↥K)ˣ, Φ (NK.GlobalCFT.Idele.principalIdele ↥K x) = 1)
    (hΦnorm : ∀ y : NK.GlobalCFT.Idele ↥F, Φ (NK.GlobalCFT.Idele.normIdeleHom ↥K ↥F y) = 1)
    (hTfix : (∏ 𝔭 ∈ T', χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a)))) = 1) :
    χ (Φ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))) = 1 := by
  classical
  letI : CommGroup (↥F ≃ₐ[↥K] ↥F) := { mul_comm := fun a b => mul_comm' a b }
  -- `↥K` has no real place
  have hnoReal : ∀ w : NumberField.InfinitePlace ↥K, w.IsComplex :=
    noRealPlace_of_hKimag_zeta p K ζ hζ hKimag
  -- the idèle decomposition `(a)ᵥ = P · D · u`
  obtain ⟨u, hu, hdec⟩ :=
    Work.GrunwaldEscapeCore.L1Korth.idele_decomposition_tFreePart p ↥K T' a
  set P : NK.GlobalCFT.Idele ↥K :=
    ∏ 𝔭 ∈ T', NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a) with hP
  set D : NK.GlobalCFT.Idele ↥K :=
    NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a) with hD
  -- the `T'`-part is killed by `χ ∘ Φ`
  have hPkill : χ (Φ P) = 1 := by
    rw [hP, map_prod, map_prod]
    exact hTfix
  -- hence `χ (Φ D) = (χ (Φ u))⁻¹`
  have hrel : χ (Φ D) = (χ (Φ u))⁻¹ := by
    have h1 : (1 : Multiplicative (ZMod p)) = χ (Φ P) * χ (Φ D) * χ (Φ u) := by
      have h : χ (Φ (NK.GlobalCFT.Idele.principalIdele ↥K a)) =
          χ (Φ P) * χ (Φ D) * χ (Φ u) := by
        rw [hdec, map_mul, map_mul, map_mul, map_mul]
      rw [hΦprin a, map_one] at h
      exact h
    rw [hPkill, one_mul] at h1
    exact mul_eq_one_iff_eq_inv.mp h1.symm
  -- it remains to see that `u` itself is killed, and this only uses that `F/↥K` is unramified
  -- outside `T'` and that `↥K` has no real place
  have hukill : χ (Φ u) = 1 := by
    -- the `p`-th roots of the components of `u` at the primes of `T'`
    have hroot : ∀ 𝔭 ∈ T', ∃ y : (NK.GlobalCFT.Place.localField ↥K
        (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ, y ^ p = u (NK.GlobalCFT.Place.ofFinite 𝔭) := by
      intro 𝔭 h𝔭
      have hmem := (Work.SSGRoute.mem_powTIdeles.mp hu).1 𝔭 h𝔭
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
      exact ⟨y, by rw [← hy, powMonoidHom_apply]⟩
    let r : (𝔭 : NK.Chebotarev.PrimeIdeal ↥K) →
        (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ :=
      fun 𝔭 => if h : 𝔭 ∈ T' then (hroot 𝔭 h).choose else 1
    have hr : ∀ 𝔭 ∈ T', (r 𝔭) ^ p = u (NK.GlobalCFT.Place.ofFinite 𝔭) := by
      intro 𝔭 h𝔭
      simp only [r, dif_pos h𝔭]
      exact (hroot 𝔭 h𝔭).choose_spec
    set c0 : NK.GlobalCFT.Idele ↥K :=
      ∏ 𝔭 ∈ T', NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) (r 𝔭) with hc0
    set u' : NK.GlobalCFT.Idele ↥K := u * (c0 ^ p)⁻¹ with hu'
    have hu_eq : u = u' * c0 ^ p := by
      rw [hu']; group
    -- `c0` is `1` away from the primes of `T'`
    have hc0_away : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
        c0 (NK.GlobalCFT.Place.ofFinite 𝔮) = 1 := by
      intro 𝔮 h𝔮
      rw [hc0]
      exact Work.GrunwaldEscapeCore.L1Korth.prod_onePlace_apply_of_not_mem T' r h𝔮
    -- the component of `c0 ^ p` at a prime of `T'` is the component of `u`
    have hc0_mem : ∀ 𝔭 ∈ T', (c0 ^ p) (NK.GlobalCFT.Place.ofFinite 𝔭) =
        u (NK.GlobalCFT.Place.ofFinite 𝔭) := by
      intro 𝔭 h𝔭
      have h1 : c0 (NK.GlobalCFT.Place.ofFinite 𝔭) = r 𝔭 := by
        rw [hc0]
        exact Work.GrunwaldEscapeCore.L1Korth.prod_onePlace_apply_of_mem T' r h𝔭
      rw [show (c0 ^ p) (NK.GlobalCFT.Place.ofFinite 𝔭) =
          (c0 (NK.GlobalCFT.Place.ofFinite 𝔭)) ^ p from rfl, h1]
      exact hr 𝔭 h𝔭
    -- `u'` is `1` on `T'` and a local unit elsewhere
    have hu'_T : ∀ 𝔭 ∈ T', u' (NK.GlobalCFT.Place.ofFinite 𝔭) = 1 := by
      intro 𝔭 h𝔭
      rw [hu', NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hc0_mem 𝔭 h𝔭,
        mul_inv_cancel]
    have hu'_unit : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
        u' (NK.GlobalCFT.Place.ofFinite 𝔮) ∈
          NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔮) := by
      intro 𝔮 h𝔮
      have hpv : NK.GlobalCFT.Place.ofFinite 𝔮 ∉ Work.SSGRoute.powAtPlaces ↥K T' := by
        intro hmem
        exact h𝔮 (hmem 𝔮 rfl)
      have hu'val : u' (NK.GlobalCFT.Place.ofFinite 𝔮) = u (NK.GlobalCFT.Place.ofFinite 𝔮) := by
        rw [hu', NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply,
          show (c0 ^ p) (NK.GlobalCFT.Place.ofFinite 𝔮) =
            (c0 (NK.GlobalCFT.Place.ofFinite 𝔮)) ^ p from rfl,
          hc0_away 𝔮 h𝔮, one_pow, inv_one, mul_one]
      rw [hu'val]
      exact (Work.SSGRoute.mem_powTIdeles.mp hu).2 _ hpv
    -- `u'` is an idèle norm
    have hu'_norm : u' ∈ NK.GlobalCFT.Idele.normImage ↥K ↥F :=
      mem_normImage_of_localUnits_of_trivialOn T' u' hu'_T hLT hu'_unit hnoReal
    have hΦu' : Φ u' = 1 := by
      obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hu'_norm
      have hy' : u' = NK.GlobalCFT.Idele.normIdeleHom ↥K ↥F y :=
        NK.GlobalCFT.Idele.ext (fun v => by rw [hy v, NK.GlobalCFT.Idele.normIdeleHom_apply])
      rw [hy']
      exact hΦnorm y
    -- and `χ` kills the `p`-th power of `Φ c0`
    have hpow : (χ (Φ c0)) ^ p = 1 := by
      have h : (χ (Φ c0)) ^ p = Multiplicative.ofAdd ((p : ℕ) • (χ (Φ c0)).toAdd) :=
        (ofAdd_nsmul p (χ (Φ c0)).toAdd).symm
      rw [h]
      have hz : ((p : ℕ) • (χ (Φ c0)).toAdd : ZMod p) = 0 := by
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rw [hz]
      rfl
    calc χ (Φ u) = χ (Φ (u' * c0 ^ p)) := by rw [hu_eq]
      _ = χ (Φ u' * Φ (c0 ^ p)) := by rw [map_mul]
      _ = χ (Φ u') * χ (Φ (c0 ^ p)) := by rw [map_mul]
      _ = χ (1 : ↥F ≃ₐ[↥K] ↥F) * χ (Φ (c0 ^ p)) := by rw [hΦu']
      _ = χ (Φ (c0 ^ p)) := by rw [map_one, one_mul]
      _ = (χ (Φ c0)) ^ p := by rw [map_pow, map_pow]
      _ = 1 := hpow
  show χ (Φ D) = 1
  rw [hrel, hukill, inv_one]

end Work.SSGRoute.N2v2
