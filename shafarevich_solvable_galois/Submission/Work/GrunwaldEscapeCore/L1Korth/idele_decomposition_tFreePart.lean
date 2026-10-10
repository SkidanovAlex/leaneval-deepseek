import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.step4_y_escape_v2.Orthogonality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèle decomposition of a global unit along its `T'`-free part

For a global unit `a ∈ Kˣ` and a finite set `T'` of finite primes of a number field `K`, the
principal idèle `(a)ᵥ` decomposes as

  `(a)ᵥ = (∏_{𝔭 ∈ T'} e_𝔭(a)) · fracIdele (tFreePart T' a) · u`

with `u ∈ powTIdeles K p T'`: the `T'`-part of `(a)ᵥ` is the product of the "one place" idèles
carrying the local images of `a`, the `T'`-free part is the idèle attached to the fractional ideal
`tFreePart T' a` (whose `𝔮`-adic exponents agree with those of `a` away from `T'` and vanish on
`T'`), and the correction `u` is a `p`-th power at the primes of `T'` and a local unit away from
them.

Concretely the correction is

  `u = (∏_{𝔭 ∈ T'} e_𝔭(a))⁻¹ · (fracIdele (tFreePart T' a))⁻¹ · (a)ᵥ`:

at a prime `𝔭 ∈ T'` the two first factors cancel the value of `(a)ᵥ` and `u` is `1` (a `p`-th
power); at a prime `𝔮 ∉ T'` the product of "one place" idèles is trivial and the remaining factor is
`(unifUnit 𝔮 ^ exp_𝔮 a)⁻¹ · a_𝔮`, which is a local unit because `unifUnit 𝔮` realises exactly the
valuation of `a_𝔮`.

This is the statement consumed by the `L₁ = K` lane of the Grünwald–Wang escape: it exhibits the
principal idèle inside `im(Kˣ) · powTIdeles`, so that the reading-off lemmas
(`Work.SSGRoute.readOff_gesU` and its relatives) apply to `fracIdele (tFreePart T' a)`.
-/

namespace Work.GrunwaldEscapeCore.L1Korth

/-- The value at `ofFinite 𝔭`, for `𝔭 ∈ T`, of the finite product of one-place idèles carrying
`g 𝔮` at `ofFinite 𝔮`: only the factor `𝔮 = 𝔭` contributes, the others being `1` there. -/
theorem prod_onePlace_apply_of_mem {K : Type} [Field K] [NumberField K]
    (T : Finset (NK.Chebotarev.PrimeIdeal K))
    (g : (𝔭 : NK.Chebotarev.PrimeIdeal K) →
      (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ)
    {𝔭 : NK.Chebotarev.PrimeIdeal K} (h𝔭 : 𝔭 ∈ T) :
    (∏ 𝔮 ∈ T, NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) (g 𝔮))
        (NK.GlobalCFT.Place.ofFinite 𝔭) = g 𝔭 := by
  rw [show (∏ 𝔮 ∈ T, NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) (g 𝔮))
        (NK.GlobalCFT.Place.ofFinite 𝔭)
      = ∏ 𝔮 ∈ T, (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) (g 𝔮))
          (NK.GlobalCFT.Place.ofFinite 𝔭)
      from map_prod (NK.GlobalCFT.Idele.eval (NK.GlobalCFT.Place.ofFinite 𝔭))
        (fun 𝔮 => NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) (g 𝔮)) T]
  rw [Finset.prod_eq_single_of_mem 𝔭 h𝔭]
  · exact NK.HassePrinciple.onePlace_apply_self _ _
  · intro b hb hne
    exact NK.HassePrinciple.onePlace_apply_ne (v := NK.GlobalCFT.Place.ofFinite 𝔭)
      (w := NK.GlobalCFT.Place.ofFinite b) (by
        intro h
        exact hne (NK.GlobalCFT.Place.ofFinite_inj.mp h.symm)) (g b)

/-- The value at `ofFinite 𝔮`, for `𝔮 ∉ T`, of the finite product of one-place idèles carrying
`g 𝔭` at `ofFinite 𝔭`: no factor sits at `ofFinite 𝔮`, so the value is `1`. -/
theorem prod_onePlace_apply_of_not_mem {K : Type} [Field K] [NumberField K]
    (T : Finset (NK.Chebotarev.PrimeIdeal K))
    (g : (𝔭 : NK.Chebotarev.PrimeIdeal K) →
      (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ)
    {𝔮 : NK.Chebotarev.PrimeIdeal K} (h𝔮 : 𝔮 ∉ T) :
    (∏ 𝔮' ∈ T, NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮') (g 𝔮'))
        (NK.GlobalCFT.Place.ofFinite 𝔮) = 1 := by
  rw [show (∏ 𝔮' ∈ T, NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮') (g 𝔮'))
        (NK.GlobalCFT.Place.ofFinite 𝔮)
      = ∏ 𝔮' ∈ T, (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮') (g 𝔮'))
          (NK.GlobalCFT.Place.ofFinite 𝔮)
      from map_prod (NK.GlobalCFT.Idele.eval (NK.GlobalCFT.Place.ofFinite 𝔮))
        (fun 𝔮' => NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮') (g 𝔮')) T]
  refine Finset.prod_eq_one (fun b hb => ?_)
  exact NK.HassePrinciple.onePlace_apply_ne (v := NK.GlobalCFT.Place.ofFinite 𝔮)
    (w := NK.GlobalCFT.Place.ofFinite b) (by
      intro h
      have : b = 𝔮 := (NK.GlobalCFT.Place.ofFinite_inj.mp h).symm
      exact h𝔮 (this ▸ hb)) (g b)

/-- The `𝔮`-adic exponent of the idèle attached to a fractional ideal is its multiplicity at
`𝔮`: `fracIdele` is `ideleOfFun` with exponent function `count K · 𝔵`. -/
theorem exp_fracIdele {K : Type} [Field K] [NumberField K]
    (𝔵 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    (q : NK.Chebotarev.PrimeIdeal K) :
    NK.GlobalCFT.Idele.exp q (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵)
      = FractionalIdeal.count K q 𝔵 :=
  NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun (fun q => FractionalIdeal.count K q 𝔵)
    (FractionalIdeal.finite_factors 𝔵) q

theorem idele_decomposition_tFreePart (p : ℕ) (K : Type) [Field K] [NumberField K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ) :
    ∃ u ∈ Work.SSGRoute.powTIdeles K p T',
      NK.GlobalCFT.Idele.principalIdele K a =
        (∏ 𝔭 ∈ T', NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔭) a)) *
        NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart T' a) * u := by
  classical
  -- The `T'`-part of `(a)ᵥ` and the `T'`-free part of its divisor.
  set P := ∏ 𝔭 ∈ T', NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔭) a) with hP
  set F := NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart T' a) with hF
  refine ⟨P⁻¹ * F⁻¹ * NK.GlobalCFT.Idele.principalIdele K a, ?_, ?_⟩
  · -- The correction `u` lies in `E_{T',p}`: `p`-th power on `T'`, local unit away from `T'`.
    rw [Work.SSGRoute.mem_powTIdeles]
    refine ⟨?_, ?_⟩
    · -- At `𝔭 ∈ T'` the correction is `1`.
      intro 𝔭 h𝔭
      have hval : (P⁻¹ * F⁻¹ * NK.GlobalCFT.Idele.principalIdele K a)
          (NK.GlobalCFT.Place.ofFinite 𝔭) = 1 := by
        have hP𝔭 : P (NK.GlobalCFT.Place.ofFinite 𝔭) =
            NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔭) a := by
          rw [hP]
          exact prod_onePlace_apply_of_mem T'
            (fun 𝔮 => NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮) a) h𝔭
        have hF𝔭 : F (NK.GlobalCFT.Place.ofFinite 𝔭) = 1 := by
          rw [hF, Work.SSGRoute.fracIdele_apply_ofFinite, Work.SSGRoute.tFreePart_count,
              Work.SSGRoute.tFreeExp_of_mem T' a h𝔭, zpow_zero]
        have hprin : (NK.GlobalCFT.Idele.principalIdele K a)
            (NK.GlobalCFT.Place.ofFinite 𝔭) =
            NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔭) a := rfl
        rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.mul_apply,
            NK.GlobalCFT.Idele.inv_apply, NK.GlobalCFT.Idele.inv_apply, hP𝔭, hF𝔭, hprin,
            inv_one, mul_one]
        exact inv_mul_cancel _
      rw [hval]
      exact Subgroup.one_mem _
    · -- Away from the places above `T'` the correction is a local unit.
      intro v hv
      rcases v with w | 𝔮
      · -- Archimedean places: `localUnits` is everything.
        rw [NK.GlobalCFT.Place.localUnits_ofInfinite]
        exact Subgroup.mem_top _
      · -- Finite `𝔮 ∉ T'`: the `𝔮`-adic exponent of the correction is `0`.
        have h𝔮 : 𝔮 ∉ T' := by
          intro hmemT
          refine hv (fun 𝔭 h => ?_)
          rw [NK.GlobalCFT.Place.ofFinite_inj.mp h]
          exact hmemT
        rw [NK.NUV2.RouteB.RayModulus.mem_localUnits_iff_exp_eq_zero]
        have hPexp : NK.GlobalCFT.Idele.exp 𝔮 P = 0 := by
          rw [hP]
          refine NK.GlobalCFT.Idele.exp_eq_zero_of_mem_localUnits ?_
          rw [prod_onePlace_apply_of_not_mem T'
            (fun 𝔮' => NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite 𝔮') a) h𝔮]
          exact Subgroup.one_mem _
        have hFexp : NK.GlobalCFT.Idele.exp 𝔮 F = Work.SSGRoute.tFreeExp T' a 𝔮 := by
          rw [hF, exp_fracIdele (Work.SSGRoute.tFreePart T' a) 𝔮,
              Work.SSGRoute.tFreePart_count]
        rw [NK.GlobalCFT.Idele.exp_mul, NK.GlobalCFT.Idele.exp_mul,
            NK.NUV2.RouteB.RayModulus.exp_inv, NK.NUV2.RouteB.RayModulus.exp_inv,
            hPexp, hFexp, Work.SSGRoute.tFreeExp_of_not_mem T' a h𝔮]
        ring
  · -- The decomposition itself: `P * F * (P⁻¹ * F⁻¹ * (a)ᵥ) = (a)ᵥ`.
    have h : P⁻¹ * F⁻¹ = (P * F)⁻¹ := by rw [mul_inv, mul_comm]
    rw [h, ← mul_assoc, mul_inv_cancel, one_mul]

end Work.GrunwaldEscapeCore.L1Korth
