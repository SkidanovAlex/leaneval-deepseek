import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.EscapeCoreLib.readOffSupPow
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime
import Submission.Work.SSGRoute.SSG8Escape.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSG8Escape

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.style.haveILetI false

/-! ## Bookkeeping: `gesUPow` in the form consumed by the reading-off lemma

`Work.SSGRoute.EscapeCoreLib.readOffSupPow` takes its hypothesis in the shape
`(im(Kˣ · E)) ⊔ (p-th powers)`, where the `p`-th powers are presented as the subgroup generated
by the `p`-th powers (`pPowSubgroup`), while `Work.SSGRoute.SSG8Escape.gesUPow` presents them as the
range of the `p`-th power homomorphism.  The two subgroups are the same. -/

theorem pPowSubgroup_eq_range_pow (p : ℕ) (G : Type*) [CommGroup G] :
    Work.SSGRoute.EscapeCoreLib.pPowSubgroup p G =
      (MonoidHom.mk' (fun x : G => x ^ p) (fun a b => mul_pow a b p)).range := by
  rw [Work.SSGRoute.EscapeCoreLib.pPowSubgroup]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro _ ⟨g, rfl⟩
    exact Work.SSGRoute.EscapeCoreLib.pow_mem_pPowSubgroup g

theorem gesUPow_eq (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (T' : Finset (NK.Chebotarev.PrimeIdeal K)) :
    Work.SSGRoute.SSG8Escape.gesUPow K p T' =
      ((NK.GlobalCFT.Idele.principalSubgroup K ⊔ Work.SSGRoute.powTIdeles K p T').map
        (NK.GlobalCFT.IdeleClassGroup.mk K)) ⊔
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (NK.GlobalCFT.IdeleClassGroup K) := by
  unfold Work.SSGRoute.SSG8Escape.gesUPow Work.SSGRoute.GrunwaldEscapeCore.gesU
  rw [pPowSubgroup_eq_range_pow]

/-! ## The reading-off correction against `U_p = gesU ⊔ (p-th powers)`

This is `Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime` with the reading-off step relaxed
to membership modulo `p`-th powers (`Work.SSGRoute.EscapeCoreLib.readOffSupPow`): the class of the
idèle of a `T'`-free fractional ideal `𝔵` now only has to lie in `U_p = gesU ⊔ (p-th powers)`.
Since the extra `p`-th powers contribute nothing to `localPowClass` at `T'` and nothing mod `p` to
the `𝔮`-adic exponents, the conclusion is unchanged. -/
theorem gesCorrectionFromPrimePow (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (p : Ω) < 1 →
      ∃ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (a : (↥K)ˣ)
    (𝔵 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K)
    (h𝔵T : ∀ 𝔭 ∈ T', FractionalIdeal.count ↥K 𝔭 𝔵 = 0)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔵div : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      𝔭 ∉ T' → 𝔭 ≠ 𝔮 → FractionalIdeal.count ↥K 𝔭 𝔵 =
        FractionalIdeal.count ↥K 𝔭
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K)))
    (h𝔵𝔮 : 𝔮 ∉ T' → FractionalIdeal.count ↥K 𝔮 𝔵 =
        FractionalIdeal.count ↥K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K)) + 1)
    (hmem : NK.GlobalCFT.IdeleClassGroup.mk ↥K
        (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵) ∈
      Work.SSGRoute.SSG8Escape.gesUPow ↥K p T') :
    ∃ b : (↥K)ˣ,
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) ≠
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) →
        B.comap (algebraMap ↥K Ω) ≠
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) := by
  classical
  -- ## Step 1: read off the subgroup `U_p = gesU ⊔ (p-th powers)`
  obtain ⟨γ, hγT, hγdiv⟩ :=
    Work.SSGRoute.EscapeCoreLib.readOffSupPow (K := ↥K) p T' 𝔵 h𝔵T
      (by simpa only [gesUPow_eq] using hmem)
  refine ⟨a * γ⁻¹, ?_, ?_⟩
  · -- ## Step 2: the Kummer characters of `a` and of `a · γ⁻¹` agree at `T`
    intro A hA σ
    have hAfin : SSGRoute.IsFinPlace k A := hTfin A hA
    obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
    -- `γ` is a local `p`-th power at `𝔭`, hence so is `γ⁻¹`, so the local classes of `a` and of
    -- `a · γ⁻¹` at `𝔭` agree
    have hγ1 : Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω)
        (K := K) (ζ := ζ) (hζ := hζ) (A := A) hAfin γ = 1 :=
      (Work.SSGRoute.ZConstruction.kummerCharMonoidHom_eq_one_iff (p := p) (k := k) (Ω := Ω)
        (K := K) (ζ := ζ) (hζ := hζ) (A := A) hAfin 𝔭 h𝔭A γ).mpr (hγT 𝔭 h𝔭T')
    have hγinv : Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω)
        (K := K) (ζ := ζ) (hζ := hζ) (A := A) hAfin γ⁻¹ = 1 := by
      rw [map_inv, hγ1, inv_one]
    haveI hsepK : IsSepClosure ↥K Ω := ⟨inferInstance, inferInstance⟩
    have hkey := Work.SSGRoute.ZConstruction.kummerCharZMod_mul_eq_of_kummerCharMonoidHom_eq_one'
      (p := p) (k := k) (Ω := Ω) (K := K) ζ hζ A hAfin a γ⁻¹ hγinv
      (Work.SSGRoute.gesLocalToGalK K σ)
      (Work.SSGRoute.GrunwaldEscapeCore.gesLocalToGalK_mem_decomp K σ)
    exact hkey.symm
  · -- ## Step 3: `b = a · γ⁻¹` is unramified outside `T' ∪ {𝔮}`
    intro B hB hnotT' hnot𝔮 σ hσ hI
    -- the `K`-prime `𝔭B` below `B`
    obtain ⟨𝔭B, h𝔭B⟩ :=
      Work.SSGRoute.GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K B hB
    have h𝔭B_notT' : 𝔭B ∉ T' := fun h => hnotT' 𝔭B h h𝔭B
    have h𝔭B_ne𝔮 : 𝔭B ≠ 𝔮 := fun h => hnot𝔮 (h ▸ h𝔭B)
    -- the `𝔭B`-adic exponent of `b = a · γ⁻¹`
    have hcount : FractionalIdeal.count ↥K 𝔭B
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((a * γ⁻¹ : (↥K)ˣ) : ↥K)) =
        FractionalIdeal.count ↥K 𝔭B
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
              (a : ↥K)) -
          FractionalIdeal.count ↥K 𝔭B
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
              (γ : ↥K)) :=
      Work.SSGRoute.GrunwaldEscapeCore.count_spanSingleton_units_mul_inv (K := ↥K) 𝔭B a γ
    -- hence `p` divides it, by the read-off and the divisor hypothesis
    have hdiv : (p : ℤ) ∣ FractionalIdeal.count ↥K 𝔭B
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((a * γ⁻¹ : (↥K)ˣ) : ↥K)) := by
      rw [hcount, ← h𝔵div 𝔭B h𝔭B_notT' h𝔭B_ne𝔮]
      exact hγdiv 𝔭B
    -- split `b` as a `p`-th power times a unit at `𝔭B`
    obtain ⟨c, u, hcu, hcount_u⟩ :=
      Work.SSGRoute.GrunwaldEscapeCore.exists_pow_mul_unit_of_dvd_count (K := ↥K) p
        (Fact.out : p.Prime).ne_zero 𝔭B (a * γ⁻¹) hdiv
    -- being a `𝔭B`-adic unit means being a unit at `B`
    have hu : B.valuation (algebraMap ↥K Ω (u : ↥K)) = 1 :=
      (Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero
        (K := ↥K) (Ω := Ω) B 𝔭B h𝔭B u).mpr hcount_u
    exact Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd k Ω K p ζ hζ B hB
      (by
        intro hlt
        obtain ⟨𝔭, h𝔭T', h𝔭eq⟩ := hT'p B hB hlt
        exact hnotT' 𝔭 h𝔭T' h𝔭eq)
      (a * γ⁻¹) ⟨c, u, hcu, hu⟩ (Work.SSGRoute.gesGalKOfFixing K σ hσ)
      (Work.SSGRoute.GrunwaldEscapeCore.gesInertia_of_gesGalKOfFixing K B σ hσ hI)

theorem correction_ssg8 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (p : Ω) < 1 →
      ∃ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (a : (↥K)ˣ)
    (𝔮 : NK.Chebotarev.PrimeIdeal ↥K) (h𝔮T' : 𝔮 ∉ T')
    (hmem : NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) *
        NK.GlobalCFT.IdeleClassGroup.mk ↥K
          (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a)) ∈
        Work.SSGRoute.SSG8Escape.gesUPow ↥K p T') :
    ∃ b : (↥K)ˣ,
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) ≠
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) →
        B.comap (algebraMap ↥K Ω) ≠
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) := by
  classical
  -- The fractional ideal `𝔵 := 𝔡 · (𝔮)`, where `𝔡 = tFreePart T' a` is the `T'`-free part of the
  -- divisor of `a` and `(𝔮)` is the prime ideal at the escape prime.
  -- ## 1. The `𝔮`-adic exponents of the prime ideal
  have hcount𝔮 : ∀ q : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K),
      FractionalIdeal.count ↥K q (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf =
        (if q = 𝔮 then 1 else 0) := by
    intro q
    rw [NK.GlobalCFT.Idele.count_idealOf]
    show NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.IdeleClassGroup.ideleOfFun ↥K
      (fun q' => if q' = 𝔮 then 1 else 0) _) = _
    rw [NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]
  -- ## 2. The `𝔮`-adic exponents of `𝔵`
  have hcount𝔵 : ∀ q : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K),
      FractionalIdeal.count ↥K q (Work.SSGRoute.tFreePart (K := ↥K) T' a *
          (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf) =
        Work.SSGRoute.tFreeExp (K := ↥K) T' a q + (if q = 𝔮 then 1 else 0) := by
    intro q
    rw [FractionalIdeal.count_mul ↥K q
        (show Work.SSGRoute.tFreePart (K := ↥K) T' a ≠ 0 from
          Idele.idealOf_ne_zero (Work.SSGRoute.tFreeIdle (K := ↥K) T' a))
        (Idele.idealOf_ne_zero (NK.HeckeL.ideleOfPrime ↥K 𝔮)),
      Work.SSGRoute.tFreePart_count, hcount𝔮 q]
  -- ## 3. The class of `fracIdele 𝔵` is the product of the two given classes
  have hfrac𝔮 : NK.NUV2.RouteB.RayModulus.fracIdele
      ((NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf) = NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
    rw [NK.NUV2.RouteB.RayModulus.fracIdele_idealOf]
    refine (NK.HeckeL.Basic.IdeleFun.congr _ _ ?_).trans rfl
    funext q
    show NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.IdeleClassGroup.ideleOfFun ↥K
      (fun q' => if q' = 𝔮 then 1 else 0) _) = _
    rw [NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]
  have hfrac𝔵 : NK.NUV2.RouteB.RayModulus.fracIdele
      (Work.SSGRoute.tFreePart (K := ↥K) T' a *
        (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf) =
      NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a) *
        NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
    rw [NK.NUV2.RouteB.RayModulus.fracIdele_mul
        (show Work.SSGRoute.tFreePart (K := ↥K) T' a ≠ 0 from
          Idele.idealOf_ne_zero (Work.SSGRoute.tFreeIdle (K := ↥K) T' a))
        (Idele.idealOf_ne_zero (NK.HeckeL.ideleOfPrime ↥K 𝔮)), hfrac𝔮]
  -- ## 4. Assemble
  refine gesCorrectionFromPrimePow p k Ω K ζ hζ T hTfin T' hTbelow hT'p a
    (Work.SSGRoute.tFreePart (K := ↥K) T' a * (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf)
    ?_ 𝔮 ?_ ?_ ?_
  · -- `𝔵` is coprime to `T'`
    intro 𝔭 h𝔭
    have h𝔭𝔮 : 𝔭 ≠ 𝔮 := fun h => h𝔮T' (h ▸ h𝔭)
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero, Work.SSGRoute.tFreeExp_of_mem T' a h𝔭]
  · -- away from `T'` and `𝔮`, the divisor of `𝔵` is that of `a`
    intro 𝔭 h𝔭T h𝔭𝔮
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero, Work.SSGRoute.tFreeExp_of_not_mem T' a h𝔭T,
      ← Idele.count_idealOf (Idele.principalIdele ↥K a), Idele.idealOf_principalIdele]
  · -- at `𝔮` the divisor of `𝔵` is that of `a` plus one
    intro h𝔮T
    rw [hcount𝔵 𝔮, if_pos rfl, Work.SSGRoute.tFreeExp_of_not_mem T' a h𝔮T,
      ← Idele.count_idealOf (Idele.principalIdele ↥K a), Idele.idealOf_principalIdele]
  · -- the class of `fracIdele 𝔵` lies in `U_p`
    rw [hfrac𝔵, map_mul]
    simpa only [mul_comm] using hmem

end Work.SSG8Escape
