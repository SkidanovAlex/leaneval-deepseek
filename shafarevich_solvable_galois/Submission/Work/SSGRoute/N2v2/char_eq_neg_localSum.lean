import Mathlib
import Submission.Work.SSGRoute.step4_y_escape_v2.Orthogonality
import Submission.Work.SSGRoute.step4_y_escape_v2.localFactor_productFormula_clean
import Submission.Work.SSGRoute.GrunwaldEscapeCore.kummerChar_artinSym_fracIdele_eq_sum
import Submission.Work.SSGRoute.GrunwaldEscapeCore.ideleOfFun_prod
import Submission.Work.SSGRoute.GrunwaldEscapeCore.productFormula_sum
import Submission.Work.SSGRoute.SSG8Escape.Setup
import Submission.Work.SSGRoute.ZDataMup.localFactor_unramified_eq_frob_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.N2v2

set_option maxHeartbeats 2000000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open NK.GlobalCFT

/-! ## Two auxiliary lemmas

Both are statements about a family of local factors `θ` of an abelian Artin map, which is exactly
the data the target theorem is handed (`hθker`, `hθfrob`, `hθprod`). -/

/-- **The local factor at an unramified prime is the Frobenius raised to the `𝔮`-adic exponent.**
Writing the local image of `x ∈ Kˣ` as `ϖ_𝔮^n · u` with `u` a local unit, the local units are local
norms at an unramified place (so `θ_𝔮` kills them, through `hθker`) and `ϖ_𝔮` is normalised to
`Frob_𝔮` (through `hθfrob`); the exponent `n` is `Idele.exp 𝔮 (principalIdele K x)`. -/
theorem theta_localFactor_frob_pow {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (θ : (v : NK.GlobalCFT.Place K) →
      (NK.GlobalCFT.Place.localField K v)ˣ →* (L ≃ₐ[K] L))
    (hθker : ∀ v, (θ v).ker =
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v)
    (hθfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K,
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔮 →
      θ (NK.GlobalCFT.Place.ofFinite 𝔮)
        (NK.GlobalCFT.IdeleClassGroup.unifUnit K 𝔮) =
        NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔮)
    (𝔮 : NK.Chebotarev.PrimeIdeal K) (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔮)
    (x : Kˣ) :
    θ (NK.GlobalCFT.Place.ofFinite 𝔮)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔮 ^
        (NK.GlobalCFT.Idele.exp 𝔮 (NK.GlobalCFT.Idele.principalIdele K x)) := by
  classical
  -- decompose the local image of `x` as `ϖ^n · u` with `u` a local unit
  obtain ⟨n, u, hu, hdec⟩ := NK.CFTLib.HR.exists_zpow_unifUnit_mul_mem_localUnits (K := K) 𝔮
    (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x)
  -- a local unit is a local norm at the unramified prime, hence killed by `θ_𝔮`
  have hker : θ (NK.GlobalCFT.Place.ofFinite 𝔮) u = 1 := by
    rw [← MonoidHom.mem_ker, hθker]
    exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified (K := K) (L := L) 𝔮
      hunr hu
  -- the valuation of the local image of `x` is `exp (-n)`
  have hval : Valued.v (((NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x :
      (𝔮.adicCompletion K)ˣ)) : 𝔮.adicCompletion K) = WithZero.exp (-n) := by
    rw [hdec, Units.val_mul, map_mul, NK.GlobalCFT.IdeleClassGroup.valued_unifUnit_zpow,
      (NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp hu, mul_one]
  -- hence `n` is the `𝔮`-adic exponent of the global element
  have hexp : NK.GlobalCFT.Idele.exp 𝔮 (NK.GlobalCFT.Idele.principalIdele K x) = n := by
    have hfn : NK.CFTLib.finVal K 𝔮
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) x) = n := by
      rw [NK.CFTLib.finVal, hval, WithZero.log_exp]
      ring
    rw [← hfn]
    rfl
  rw [hexp, hdec, map_mul, map_zpow, hθfrob 𝔮 hunr, hker, mul_one]

/-- **The product formula as a vanishing sum over the finite places.**

Starting from the product formula `hθprod` for the principal idèle of `a`, applied to the finite set
of places consisting of the finite primes of `s` together with *all* archimedean places (so that the
hypothesis of `hθprod` only has to be checked at the finite primes outside `s`), and observing that
`χ ∘ θ` vanishes at every archimedean place (`harch`), the sum of the local terms over `s` is `0`. -/
theorem sum_localFactors_eq_zero (p : ℕ) [Fact p.Prime] {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (χ : (L ≃ₐ[K] L) →* Multiplicative (ZMod p))
    (θ : (v : NK.GlobalCFT.Place K) →
      (NK.GlobalCFT.Place.localField K v)ˣ →* (L ≃ₐ[K] L))
    (hθprod : ∀ (x : Kˣ) (s : Finset (NK.GlobalCFT.Place K)),
      (∀ v, v ∉ s → θ v (NK.CFTLib.IdeleHasse.localImageAt v x) = 1) →
      NK.CFTLib.IdeleHasse.cprod hcomm s
        (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1)
    (a : Kˣ)
    (harch : ∀ w : NumberField.InfinitePlace K,
      (χ (θ (NK.GlobalCFT.Place.ofInfinite w)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) a))).toAdd = 0)
    (s : Finset (NK.Chebotarev.PrimeIdeal K))
    (hs : ∀ 𝔮, 𝔮 ∉ s → θ (NK.GlobalCFT.Place.ofFinite 𝔮)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) a) = 1) :
    ∑ 𝔮 ∈ s, (χ (θ (NK.GlobalCFT.Place.ofFinite 𝔮)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) a))).toAdd = 0 := by
  classical
  -- the finite set of places: the primes of `s` together with *all* archimedean places
  set s' : Finset (NK.GlobalCFT.Place K) :=
    s.image NK.GlobalCFT.Place.ofFinite ∪ Finset.univ.image NK.GlobalCFT.Place.ofInfinite with hs'
  -- every place outside `s'` is a finite prime outside `s`
  have htriv : ∀ v : NK.GlobalCFT.Place K,
      v ∉ s' → θ v (NK.CFTLib.IdeleHasse.localImageAt v a) = 1 := by
    intro v hv
    cases v with
    | inl w =>
      exact absurd (show (Sum.inl w : NK.GlobalCFT.Place K) ∈ s' from
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))) hv
    | inr q =>
      exact hs q (fun hq => hv (Finset.mem_union_left _
        (Finset.mem_image_of_mem NK.GlobalCFT.Place.ofFinite hq)))
  -- the product formula, pushed through `χ`
  have hprod : ∏ v ∈ s',
      χ (θ v (NK.CFTLib.IdeleHasse.localImageAt v a)) = 1 := by
    rw [← Work.SSGRoute.GrunwaldEscapeCore.cprod_map_prod hcomm χ s'
      (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt v a)), hθprod a s' htriv]
    exact map_one χ
  -- hence the corresponding vanishing sum
  have hsum : ∑ v ∈ s', (χ (θ v (NK.CFTLib.IdeleHasse.localImageAt v a))).toAdd = 0 := by
    rw [← Work.SSGRoute.GrunwaldEscapeCore.toAdd_prod_eq_sum p s'
      (fun v => χ (θ v (NK.CFTLib.IdeleHasse.localImageAt v a))), hprod]
    simp
  -- split off the archimedean places, which contribute `0`
  have hdisj : Disjoint (s.image NK.GlobalCFT.Place.ofFinite)
      (Finset.univ.image (NK.GlobalCFT.Place.ofInfinite (K := K))) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hv1
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hv2
    exact NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w q hw
  have hfin : ∑ v ∈ s.image NK.GlobalCFT.Place.ofFinite,
      (χ (θ v (NK.CFTLib.IdeleHasse.localImageAt v a))).toAdd
      = ∑ 𝔮 ∈ s, (χ (θ (NK.GlobalCFT.Place.ofFinite 𝔮)
          (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) a))).toAdd :=
    Finset.sum_image (fun x _ y _ h => NK.GlobalCFT.Place.ofFinite_inj.mp h)
  have hinf : ∑ v ∈ Finset.univ.image (NK.GlobalCFT.Place.ofInfinite (K := K)),
      (χ (θ v (NK.CFTLib.IdeleHasse.localImageAt v a))).toAdd = 0 := by
    rw [Finset.sum_image (fun x _ y _ h => NK.GlobalCFT.Place.ofInfinite_inj.mp h)]
    exact Finset.sum_eq_zero (fun w _ => harch w)
  rw [hs'] at hsum
  rw [Finset.sum_union hdisj] at hsum
  rw [hfin, hinf, add_zero] at hsum
  exact hsum

/-- **The reduction of the orthogonality to the local product.**

Let `M/↥K` be the class field of `U_p = gesU ↾K ⊔ (p-th powers)` (so its norm class subgroup is
`gesUPow ↥K p T'`), unramified outside `T'`, with an idèlic Artin map `art` which is
Frobenius-normalised at every unramified prime, and let `𝔡 = tFreePart T' a` be the `T'`-free part
of the divisor of the global element `a ∈ Kˣ`.

For an Artin family `θ` of local factors of `M/↥K` (kernel `= localNormSubgroup`, Frobenius at every
unramified prime, and the product formula on the principal idèles, as supplied by
`localFactor_productFormula_clean`), a multiplicative character `χ` of `Gal(M/↥K)` trivial on the
*archimedean* local factors (`hχarch`), and the ideal--idèle dictionary
(`kummerChar_artinSym_fracIdele_eq_sum`, applied at the unramified primes via `hMunr` and the
Frobenius normalisation `hfrob`), the Artin symbol of `𝔡` is computed by the local terms at `T'`:

  `χ(art 𝔡).toAdd + ∑_{𝔭 ∈ T'} χ(θ_𝔭(a_𝔭)).toAdd = 0`.

The two inputs are the ideal--idèle dictionary (the sum over the support of `𝔡`, whose primes lie
outside `T'` because `tFreePart T' a` has zero exponent on `T'`) and the product formula for the
single global element `a` (`localFactor_productFormula_clean`): at a prime `𝔮 ∉ T'` the local factor
is `Frob_𝔮 ^ v_𝔮(a)`, and `v_𝔮(a) = count 𝔮 𝔡` there, while the archimedean factors are killed by
`hχarch`. -/
theorem char_eq_neg_localSum (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (hMunr : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮)
    (hcomm : ∀ a b : (↥M ≃ₐ[↥K] ↥M), a * b = b * a)
    (χ : (↥M ≃ₐ[↥K] ↥M) →* Multiplicative (ZMod p))
    (θ : (v : NK.GlobalCFT.Place ↥K) →
      (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥M ≃ₐ[↥K] ↥M))
    (hθker : ∀ v, (θ v).ker =
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥M) v)
    (hθfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
      θ (NK.GlobalCFT.Place.ofFinite 𝔮) (NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K 𝔮) =
        NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮)
    (hθprod : ∀ (x : (↥K)ˣ) (s : Finset (NK.GlobalCFT.Place ↥K)),
      (∀ v, v ∉ s → θ v (NK.CFTLib.IdeleHasse.localImageAt v x) = 1) →
      NK.CFTLib.IdeleHasse.cprod hcomm s
        (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1)
    (hχarch : ∀ v : NK.GlobalCFT.Place ↥K, (∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
        v ≠ NK.GlobalCFT.Place.ofFinite 𝔮) →
      ∀ u : (NK.GlobalCFT.Place.localField ↥K v)ˣ, (χ (θ v u)).toAdd = 0)
    (art : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
      art (NK.HeckeL.ideleOfPrime ↥K 𝔮) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮)
    (a : (↥K)ˣ) :
    (χ (art (NK.NUV2.RouteB.RayModulus.fracIdele
        (Work.SSGRoute.tFreePart (K := ↥K) T' a)))).toAdd +
      ∑ 𝔭 ∈ T', (χ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd = 0 := by
  classical
  -- `𝔡`, the `T'`-free part of the divisor of `a`, and its support
  set 𝔡 : FractionalIdeal (nonZeroDivisors (𝓞 ↥K)) ↥K :=
    Work.SSGRoute.tFreePart (K := ↥K) T' a with h𝔡
  set supp : Finset (NK.Chebotarev.PrimeIdeal ↥K) :=
    (FractionalIdeal.finite_factors 𝔡).toFinset with hsupp
  have hcount_ne : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      (𝔮 ∈ supp ↔ FractionalIdeal.count ↥K 𝔮 𝔡 ≠ 0) := by
    intro 𝔮
    rw [hsupp]
    exact Set.Finite.mem_toFinset _
  -- (A) the ideal--idèle dictionary: `χ (art 𝔡)` is the sum over the support of `𝔡`
  have hunr_supp : ∀ 𝔮 ∈ supp, NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 := by
    intro 𝔮 h𝔮
    refine hMunr 𝔮 (fun h𝔮T => ?_)
    have hne : FractionalIdeal.count ↥K 𝔮 𝔡 ≠ 0 := (hcount_ne 𝔮).mp h𝔮
    rw [h𝔡] at hne
    exact hne (Work.SSGRoute.tFreePart_count_eq_zero (K := ↥K) T' a h𝔮T)
  have hA : (χ (art (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡))).toAdd =
      ∑ 𝔮 ∈ supp, (FractionalIdeal.count ↥K 𝔮 𝔡 : ZMod p) *
        (χ (NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮)).toAdd :=
    Work.SSGRoute.GrunwaldEscapeCore.kummerChar_artinSym_fracIdele_eq_sum p hcomm art hfrob χ 𝔡
      hunr_supp
  -- (B) the product formula for the global element `a`
  have harch : ∀ w : NumberField.InfinitePlace ↥K,
      (χ (θ (NK.GlobalCFT.Place.ofInfinite w)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) a))).toAdd = 0 :=
    fun w => hχarch (NK.GlobalCFT.Place.ofInfinite w)
      (fun 𝔮 => NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w 𝔮)
      (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) a)
  have hθtriv : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' ∪ supp →
      θ (NK.GlobalCFT.Place.ofFinite 𝔮)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) a) = 1 := by
    intro 𝔮 h𝔮
    have h𝔮T : 𝔮 ∉ T' := fun h => h𝔮 (Finset.mem_union_left _ h)
    have h𝔮S : 𝔮 ∉ supp := fun h => h𝔮 (Finset.mem_union_right _ h)
    -- outside the support of `𝔡` (and outside `T'`) the element `a` is a local unit
    have hcount0 : FractionalIdeal.count ↥K 𝔮 𝔡 = 0 := by
      by_contra hne
      exact h𝔮S ((hcount_ne 𝔮).mpr hne)
    rw [h𝔡] at hcount0
    have hexp0 : NK.GlobalCFT.Idele.exp 𝔮 (NK.GlobalCFT.Idele.principalIdele ↥K a) = 0 := by
      rw [← Work.SSGRoute.tFreePart_count_eq_exp (K := ↥K) T' a h𝔮T]
      exact hcount0
    have hmem : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) a ∈
        NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔮) :=
      (NK.NUV2.RouteB.RayModulus.mem_localUnits_iff_exp_eq_zero 𝔮
        (NK.GlobalCFT.Idele.principalIdele ↥K a)).mpr hexp0
    rw [← MonoidHom.mem_ker, hθker]
    exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified (K := ↥K) (L := ↥M)
      𝔮 (hMunr 𝔮 h𝔮T) hmem
  have hB : ∑ 𝔮 ∈ T' ∪ supp,
      (χ (θ (NK.GlobalCFT.Place.ofFinite 𝔮)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) a))).toAdd = 0 :=
    sum_localFactors_eq_zero p hcomm χ θ hθprod a harch (T' ∪ supp) hθtriv
  -- (C) `T'` and the support of `𝔡` are disjoint, and on the support the local factor is a
  -- Frobenius power
  have hdisj : Disjoint T' supp := by
    rw [Finset.disjoint_left]
    intro 𝔮 h𝔮T h𝔮S
    have hne : FractionalIdeal.count ↥K 𝔮 𝔡 ≠ 0 := (hcount_ne 𝔮).mp h𝔮S
    rw [h𝔡] at hne
    exact hne (Work.SSGRoute.tFreePart_count_eq_zero (K := ↥K) T' a h𝔮T)
  have hsuppEq : ∑ 𝔮 ∈ supp,
      (χ (θ (NK.GlobalCFT.Place.ofFinite 𝔮)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) a))).toAdd
      = ∑ 𝔮 ∈ supp, (FractionalIdeal.count ↥K 𝔮 𝔡 : ZMod p) *
          (χ (NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮)).toAdd := by
    refine Finset.sum_congr rfl (fun 𝔮 h𝔮 => ?_)
    have hne : FractionalIdeal.count ↥K 𝔮 𝔡 ≠ 0 := (hcount_ne 𝔮).mp h𝔮
    have h𝔮T : 𝔮 ∉ T' := by
      intro h
      rw [h𝔡] at hne
      exact hne (Work.SSGRoute.tFreePart_count_eq_zero (K := ↥K) T' a h)
    have hexp : NK.GlobalCFT.Idele.exp 𝔮 (NK.GlobalCFT.Idele.principalIdele ↥K a)
        = FractionalIdeal.count ↥K 𝔮 𝔡 := by
      rw [h𝔡, Work.SSGRoute.tFreePart_count_eq_exp (K := ↥K) T' a h𝔮T]
    rw [theta_localFactor_frob_pow θ hθker hθfrob 𝔮 (hMunr 𝔮 h𝔮T) a, hexp, map_zpow,
      toAdd_zpow, zsmul_eq_mul]
  -- assembly
  rw [Finset.sum_union hdisj] at hB
  rw [hA, ← hsuppEq, add_comm]
  exact hB

end Work.SSGRoute.N2v2
