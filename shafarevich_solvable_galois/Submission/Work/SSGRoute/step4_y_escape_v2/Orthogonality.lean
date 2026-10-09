import Mathlib
import Submission.Work.SSGRoute.step4_y_escape_v2.ChebotarevSplit
import Submission.Work.SSGRoute.step4_y_escape_v2.ReadOff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute

variable {K : Type} [Field K] [NumberField K]

/-! ## The `T`-free part of the divisor of a global unit

The orthogonality computation of `grunwald_escape_correction` starts from `𝔡`, the `T`-free part of
`div(a)` (`a ∈ Kˣ` the Grünwald element realising the local datum at `T`): the fractional ideal with
the *same* `𝔮`-adic exponents as `a` away from `T`, and exponent `0` at the primes of `T`.  It is
built as the ideal of the explicit idèle
`ideleOfFun K (fun 𝔮 => if 𝔮 ∈ T then 0 else exp 𝔮 (prin a))`, so that `fracIdele 𝔡` *is* that
idèle — the form in which both the reading-off and the Artin map consume it. -/

/-- The `T`-free exponent of `a` at `𝔮` (`0` on `T`, the exponent of `a` away from `T`). -/
noncomputable def tFreeExp (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    (𝔮 : NK.Chebotarev.PrimeIdeal K) : ℤ := by
  classical
  exact if 𝔮 ∈ T then 0 else Idele.exp 𝔮 (Idele.principalIdele K a)

/-- The `T`-supported part of the exponent of `a` at `𝔮`. -/
noncomputable def tSupportedExp (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    (𝔮 : NK.Chebotarev.PrimeIdeal K) : ℤ := by
  classical
  exact if 𝔮 ∈ T then Idele.exp 𝔮 (Idele.principalIdele K a) else 0

theorem tFreeExp_of_mem (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    {𝔮 : NK.Chebotarev.PrimeIdeal K} (h𝔮 : 𝔮 ∈ T) : tFreeExp T a 𝔮 = 0 := by
  rw [tFreeExp]; exact if_pos h𝔮

theorem tFreeExp_of_not_mem (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    {𝔮 : NK.Chebotarev.PrimeIdeal K} (h𝔮 : 𝔮 ∉ T) :
    tFreeExp T a 𝔮 = Idele.exp 𝔮 (Idele.principalIdele K a) := by
  rw [tFreeExp]; exact if_neg h𝔮

theorem tSupportedExp_of_mem (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    {𝔮 : NK.Chebotarev.PrimeIdeal K} (h𝔮 : 𝔮 ∈ T) :
    tSupportedExp T a 𝔮 = Idele.exp 𝔮 (Idele.principalIdele K a) := by
  rw [tSupportedExp]; exact if_pos h𝔮

theorem tSupportedExp_of_not_mem (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    {𝔮 : NK.Chebotarev.PrimeIdeal K} (h𝔮 : 𝔮 ∉ T) : tSupportedExp T a 𝔮 = 0 := by
  rw [tSupportedExp]; exact if_neg h𝔮

/-- `tFreeExp T a` is finitely supported (`T` is finite and `div a` has finite support). -/
theorem eventually_tFreeExp (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ) :
    ∀ᶠ 𝔮 in Filter.cofinite, tFreeExp T a 𝔮 = 0 := by
  rw [Filter.eventually_cofinite]
  refine (T.finite_toSet.union
    (Idele.finite_exp_support (Idele.principalIdele K a))).subset ?_
  intro 𝔮 h𝔮
  rw [Set.mem_union]
  by_cases h : 𝔮 ∈ T
  · exact Or.inl (Finset.mem_coe.mpr h)
  · refine Or.inr ?_
    have h1 : tFreeExp T a 𝔮 ≠ 0 := h𝔮
    rwa [tFreeExp_of_not_mem T a h] at h1

/-- The idèle whose `𝔮`-adic exponents are those of `a` away from `T` and `0` on `T`. -/
noncomputable def tFreeIdle (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ) : Idele K :=
  IdeleClassGroup.ideleOfFun K (tFreeExp T a) (eventually_tFreeExp T a)

/-- The `T`-free part of the divisor of `a`. -/
noncomputable def tFreePart (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  Idele.idealOf (tFreeIdle T a)

theorem exp_tFreeIdle (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    (𝔮 : NK.Chebotarev.PrimeIdeal K) :
    Idele.exp 𝔮 (tFreeIdle T a) = tFreeExp T a 𝔮 :=
  IdeleClassGroup.exp_ideleOfFun _ _ 𝔮

/-- The defining property of `tFreePart`: its `𝔮`-adic exponents agree with those of `a` away from
`T`, and vanish on `T`. -/
theorem tFreePart_count (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    (𝔮 : NK.Chebotarev.PrimeIdeal K) :
    FractionalIdeal.count K 𝔮 (tFreePart T a) = tFreeExp T a 𝔮 := by
  rw [tFreePart, Idele.count_idealOf]
  exact exp_tFreeIdle T a 𝔮

theorem tFreePart_count_eq_zero (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    {𝔮 : NK.Chebotarev.PrimeIdeal K} (h𝔮 : 𝔮 ∈ T) :
    FractionalIdeal.count K 𝔮 (tFreePart T a) = 0 := by
  rw [tFreePart_count, tFreeExp_of_mem T a h𝔮]

theorem tFreePart_count_eq_exp (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    {𝔮 : NK.Chebotarev.PrimeIdeal K} (h𝔮 : 𝔮 ∉ T) :
    FractionalIdeal.count K 𝔮 (tFreePart T a) = Idele.exp 𝔮 (Idele.principalIdele K a) := by
  rw [tFreePart_count, tFreeExp_of_not_mem T a h𝔮]

/-- `𝔡` is coprime to `T`. -/
theorem tFreePart_coprime (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ) :
    ∀ 𝔮 ∈ T, FractionalIdeal.count K 𝔮 (tFreePart T a) = 0 :=
  fun _ h𝔮 => tFreePart_count_eq_zero T a h𝔮

/-- `div(a)` equals `𝔡` times the `T`-supported part. -/
theorem exponent_eq_add_tFreePart (T : Finset (NK.Chebotarev.PrimeIdeal K)) (a : Kˣ)
    (𝔮 : NK.Chebotarev.PrimeIdeal K) :
    Idele.exp 𝔮 (Idele.principalIdele K a)
      = FractionalIdeal.count K 𝔮 (tFreePart T a) + tSupportedExp T a 𝔮 := by
  rw [tFreePart_count]
  by_cases h𝔮 : 𝔮 ∈ T
  · rw [tFreeExp_of_mem T a h𝔮, tSupportedExp_of_mem T a h𝔮]; ring
  · rw [tFreeExp_of_not_mem T a h𝔮, tSupportedExp_of_not_mem T a h𝔮]; ring

end Work.SSGRoute
