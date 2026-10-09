import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.NK.NUV2.RouteB.RayModulus.exists_ideal_of_class
import Submission.Work.SSGRoute.ges_escape_aux
import Submission.Work.SSGRoute.finiteIndex_gesU
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

theorem ideleOfFun_ofFinite (f : HeightOneSpectrum (𝓞 K) → ℤ)
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) (q : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup.ideleOfFun K f hf (NK.GlobalCFT.Place.ofFinite q)
      = NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^ (f q) := rfl

theorem fracIdele_apply_ofFinite (𝔵 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (q : HeightOneSpectrum (𝓞 K)) :
    NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 (NK.GlobalCFT.Place.ofFinite q)
      = NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^
        (FractionalIdeal.count K q 𝔵) := rfl

/-- A local `p`-th power has `p`-divisible `𝔮`-adic exponent. -/
theorem dvd_exp_of_mem_ellPowSubgroup (p : ℕ) (𝔮 : HeightOneSpectrum (𝓞 K)) (e : Idele K)
    (h : e (NK.GlobalCFT.Place.ofFinite 𝔮) ∈
      NK.UchidaKummer.ellPowSubgroup (𝔮.adicCompletion K) p) :
    (p : ℤ) ∣ Idele.exp 𝔮 e := by
  obtain ⟨c, hc⟩ := h
  rw [Idele.exp_def]
  have hc' : e (NK.GlobalCFT.Place.ofFinite 𝔮) = c ^ p := by
    rw [← hc]
    rfl
  have hv : Valued.v (R := 𝔮.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (e (NK.GlobalCFT.Place.ofFinite 𝔮) : 𝔮.adicCompletion K)
      = (Valued.v (R := 𝔮.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (c : 𝔮.adicCompletion K)) ^ p := by
    rw [hc', Units.val_pow_eq_pow_val, map_pow]
  rw [hv, WithZero.log_pow, nsmul_eq_mul]
  exact dvd_neg.mpr (dvd_mul_right _ _)

/-- **Reading off the subgroup `U = im(Kˣ · E_{T,unr})`.**  A fractional ideal `𝔵` of `K` coprime to
`T` whose idèle class lies in `U = im(Kˣ · E_{T,unr})` differs from a principal fractional ideal
`(γ)` by a `p`-th power of an ideal, where `γ` is a local `p`-th power at every prime of `T`. -/
theorem readOff_gesU (p : ℕ) [Fact p.Prime]
    (T : Finset (NK.Chebotarev.PrimeIdeal K))
    (𝔵 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (h𝔵T : ∀ 𝔭 ∈ T, FractionalIdeal.count K 𝔭 𝔵 = 0)
    (hmem : IdeleClassGroup.mk K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵) ∈
      (Idele.principalSubgroup K ⊔ powTIdeles K p T).map (IdeleClassGroup.mk K)) :
    ∃ γ : Kˣ, (∀ 𝔭 ∈ T, NK.UchidaKummer.localPowClass K p 𝔭 γ = 1) ∧
      ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K,
        (p : ℤ) ∣ FractionalIdeal.count K 𝔮 𝔵
          - FractionalIdeal.count K 𝔮
              (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (γ : K)) := by
  classical
  set a : Idele K := NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 with hadef
  have hmem' : a ∈ Idele.principalSubgroup K ⊔ powTIdeles K p T := by
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
    have h1 : y⁻¹ * a ∈ Idele.principalSubgroup K :=
      (IdeleClassGroup.mk_eq_mk_iff).mp hyeq
    have h2 : y * (y⁻¹ * a) ∈ Idele.principalSubgroup K ⊔ powTIdeles K p T :=
      Subgroup.mul_mem _ hy (Subgroup.mem_sup_left h1)
    rwa [mul_inv_cancel_left] at h2
  obtain ⟨c, hc, e, he, hce⟩ := Subgroup.mem_sup.mp hmem'
  obtain ⟨γ, rfl⟩ := Idele.mem_principalSubgroup.mp hc
  refine ⟨γ, ?_, ?_⟩
  · -- `γ` is a local `p`-th power at every prime of `T`
    intro 𝔭 h𝔭
    have he𝔭 : e (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
        NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p := (mem_powTIdeles.mp he).1 𝔭 h𝔭
    have hcomp : (Idele.principalIdele K γ) (NK.GlobalCFT.Place.ofFinite 𝔭)
        = (e (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ := by
      have h := congrArg (fun z : Idele K => z (NK.GlobalCFT.Place.ofFinite 𝔭)) hce
      rw [Idele.mul_apply] at h
      rw [show a (NK.GlobalCFT.Place.ofFinite 𝔭) = 1 from by
        rw [hadef, fracIdele_apply_ofFinite, h𝔵T 𝔭 h𝔭, zpow_zero]] at h
      exact mul_eq_one_iff_eq_inv.mp h
    have hmemγ : (Idele.principalIdele K γ) (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
        NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p := by
      rw [hcomp]
      exact Subgroup.inv_mem _ he𝔭
    rw [Idele.principalIdele_apply] at hmemγ
    have hφ : (QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p))
        ((Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom) γ) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hmemγ
    rw [NK.UchidaKummer.localPowClass]
    exact hφ
  · -- the `𝔮`-adic exponents differ by a `p`-th power
    intro 𝔮
    have hγ : FractionalIdeal.count K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (γ : K))
        = Idele.exp 𝔮 (Idele.principalIdele K γ) := by
      rw [← Idele.idealOf_principalIdele, Idele.count_idealOf]
    have hdiff : FractionalIdeal.count K 𝔮 𝔵
        - FractionalIdeal.count K 𝔮
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (γ : K))
        = Idele.exp 𝔮 e := by
      have h := congrArg (Idele.exp 𝔮) hce
      rw [Idele.exp_mul, hadef, IdeleClassGroup.exp_ideleOfFun] at h
      rw [← hγ] at h
      linarith
    rw [hdiff]
    by_cases h𝔮 : 𝔮 ∈ T
    · exact dvd_exp_of_mem_ellPowSubgroup p 𝔮 e ((mem_powTIdeles.mp he).1 𝔮 h𝔮)
    · have he0 : Idele.exp 𝔮 e = 0 :=
        (NK.NUV2.RouteB.RayModulus.mem_localUnits_iff_exp_eq_zero 𝔮 e).mp
          ((mem_powTIdeles.mp he).2 (NK.GlobalCFT.Place.ofFinite 𝔮)
            (fun hcon => h𝔮 (hcon 𝔮 rfl)))
      rw [he0]
      exact dvd_zero _

end Work.SSGRoute
