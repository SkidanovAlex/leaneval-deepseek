import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.HeckeL.Basic.ideal_eq_prod_finsupp
import Submission.NK.HeckeL.Basic.ideleOfIdeal_mul
import Submission.NK.NUV2.RouteB.RayModulus.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

namespace NK.NUV2.RouteB.RayModulus

open NK.GlobalCFT (Idele IdeleClassGroup Place)

variable {K : Type} [Field K] [NumberField K]

/-! ## The idèle of a fractional ideal and the unit part of a principal idèle -/

/-- The idèle attached to a fractional ideal: `1` at the archimedean places and the `f q`-th power
of a local uniformiser at the finite place `q`, where `f q` is the multiplicity of `q` in `I`. -/
noncomputable def ideleOfFracK (I : FractionalIdeal (𝓞 K)⁰ K) : Idele K :=
  IdeleClassGroup.ideleOfFun K (fun q => FractionalIdeal.count K q I)
    (FractionalIdeal.finite_factors I)

theorem exp_ideleOfFracK (I : FractionalIdeal (𝓞 K)⁰ K) (q : HeightOneSpectrum (𝓞 K)) :
    Idele.exp q (ideleOfFracK I) = FractionalIdeal.count K q I :=
  IdeleClassGroup.exp_ideleOfFun _ _ q

theorem idealOf_ideleOfFracK {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    Idele.idealOf (ideleOfFracK I) = I :=
  IdeleClassGroup.fractionalIdeal_eq_of_count_eq (Idele.idealOf_ne_zero _) hI
    (fun q => by rw [Idele.count_idealOf, exp_ideleOfFracK])

theorem ideleOfIdeal_eq_ideleOfFracK (I : Ideal (𝓞 K)) :
    NK.HeckeL.ideleOfIdeal K I = ideleOfFracK (I : FractionalIdeal (𝓞 K)⁰ K) := by
  refine Idele.ext fun v => ?_
  rcases v with w | q <;> rfl

theorem ideleOfFracK_mul {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    ideleOfFracK (I * J) = ideleOfFracK I * ideleOfFracK J := by
  have key : (fun q => FractionalIdeal.count K q (I * J))
      = (fun q => FractionalIdeal.count K q I) + (fun q => FractionalIdeal.count K q J) := by
    funext q
    rw [Pi.add_apply, FractionalIdeal.count_mul K q hI hJ]
  have hsum : ∀ᶠ q in Filter.cofinite,
      ((fun q => FractionalIdeal.count K q I) + (fun q => FractionalIdeal.count K q J)) q = 0 :=
    ((FractionalIdeal.finite_factors (K := K) (I := I)).and
      (FractionalIdeal.finite_factors (K := K) (I := J))).mono
      (fun q hq => by simp [Pi.add_apply, hq.1, hq.2])
  rw [ideleOfFracK, ideleOfFracK, ideleOfFracK]
  trans IdeleClassGroup.ideleOfFun K
    ((fun q => FractionalIdeal.count K q I) + (fun q => FractionalIdeal.count K q J)) hsum
  · exact NK.HeckeL.Basic.IdeleFun.congr _ _ key
  · exact (NK.HeckeL.Basic.IdeleFun.mul _ _ _ _ hsum).symm

theorem ideleOfFracK_one : ideleOfFracK (1 : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  apply Idele.ext
  intro v
  rcases v with w | q
  · rfl
  · show IdeleClassGroup.ideleOfFun K
        (fun q => FractionalIdeal.count K q (1 : FractionalIdeal (𝓞 K)⁰ K)) _ (Place.ofFinite q)
      = (1 : Idele K) (Place.ofFinite q)
    rw [NK.HeckeL.Basic.IdeleFun.apply_ofFinite, FractionalIdeal.count_one, zpow_zero]
    rfl

theorem ideleOfFracK_inv {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    ideleOfFracK I⁻¹ = (ideleOfFracK I)⁻¹ := by
  have h1 : ideleOfFracK I * ideleOfFracK I⁻¹ = 1 := by
    rw [← ideleOfFracK_mul hI (inv_ne_zero hI), mul_inv_cancel₀ hI, ideleOfFracK_one]
  exact eq_inv_of_mul_eq_one_right h1

/-- The **unit part** of the idèle of the principal ideal `(a)`: the idèle with
`ideleOfFracK ((a)) = principalIdele a * uUnitHom a`. -/
noncomputable def uUnitHom (a : Kˣ) : Idele K :=
  ideleOfFracK (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) * (Idele.principalIdele K a)⁻¹

theorem uUnitHom_apply_ofFinite (a : Kˣ) (q : HeightOneSpectrum (𝓞 K)) :
    uUnitHom a (Place.ofFinite q)
      = IdeleClassGroup.unifUnit K q ^ FractionalIdeal.count K q
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))
        * (Units.map (algebraMap K (q.adicCompletion K)) a)⁻¹ := rfl

theorem uUnitHom_apply_ofInfinite (a : Kˣ) (w : InfinitePlace K) :
    uUnitHom a (Place.ofInfinite w)
      = (Units.map (algebraMap K (Place.localField K (Place.ofInfinite w))) a)⁻¹ := by
  show (1 : (Place.localField K (Place.ofInfinite w))ˣ)
      * (Units.map (algebraMap K (Place.localField K (Place.ofInfinite w))) a)⁻¹ = _
  rw [one_mul]

theorem uUnitHom_mem_integralIdeles (a : Kˣ) : uUnitHom a ∈ Idele.integralIdeles K := by
  rw [← Idele.idealOf_eq_one_iff]
  show Idele.idealOf (ideleOfFracK (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))
    * (Idele.principalIdele K a)⁻¹) = 1
  rw [Idele.idealOf_mul, idealOf_ideleOfFracK
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero a)), Idele.idealOf_inv,
    Idele.idealOf_principalIdele, mul_inv_cancel₀]
  exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero a)

theorem ideleOfFracK_spanSingleton_eq (a : Kˣ) :
    ideleOfFracK (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))
      = Idele.principalIdele K a * uUnitHom a := by
  show ideleOfFracK (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))
      = Idele.principalIdele K a
        * (ideleOfFracK (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))
          * (Idele.principalIdele K a)⁻¹)
  rw [← mul_assoc, mul_comm (Idele.principalIdele K a) (ideleOfFracK _), mul_assoc,
    mul_inv_cancel, mul_one]

theorem classOfIdeal_eq_mk (U : Subgroup (Idele K)) (I : Ideal (𝓞 K)) :
    NK.HeckeL.classOfIdeal K U I = QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K I) := rfl

/-! ## Two bridges between `CongSubgroup` membership and `IsCongElem` -/

/-- If `α` is a unit modulo the support of `𝔪` and `IsCongElem K 𝔪 α`, then the unit part of the
idèle of `(α)` lies in the congruence subgroup `U(𝔪)`. -/
theorem uUnitHom_mem_congSubgroup {𝔪 : NK.NUV2.RouteB.Modulus K} {α : K} (hα : α ≠ 0)
    (hunit : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
      Valued.v (algebraMap K (q.adicCompletion K) α) = 1)
    (h : NK.NUV2.RouteB.IsCongElem K 𝔪 α) :
    uUnitHom (Units.mk0 α hα) ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  obtain ⟨hcong, hpos⟩ := h
  set a : Kˣ := Units.mk0 α hα with ha_def
  have ha : (a : K) = α := by rw [ha_def]; exact Units.val_mk0 hα
  rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff]
  refine ⟨?_, ?_⟩
  · intro q
    refine ⟨?_, ?_⟩
    · rw [← Place.mem_localUnits_ofFinite_iff_valued_eq_one]
      exact Idele.mem_integralIdeles.mp (uUnitHom_mem_integralIdeles a)
        (Place.ofFinite q) (Place.isFinite_ofFinite q)
    · by_cases hq : 𝔪.exps q = 0
      · have hmem := Idele.mem_integralIdeles.mp (uUnitHom_mem_integralIdeles a)
          (Place.ofFinite q) (Place.isFinite_ofFinite q)
        have hv : Valued.v (((uUnitHom a (Place.ofFinite q) : (q.adicCompletion K)ˣ) :
            q.adicCompletion K)) = 1 :=
          (Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp hmem
        have hle : Valued.v ((((uUnitHom a (Place.ofFinite q) : (q.adicCompletion K)ˣ) :
            q.adicCompletion K)) - 1) ≤ 1 :=
          Valuation.map_sub_le (v := Valued.v) (le_of_eq hv) (by simp)
        simpa [NK.NUV2.RouteB.IsCongAt, hq] using hle
      · have hval' : (HeightOneSpectrum.valuation K q) (a : K) = 1 := by
          rw [ha, ← Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq q α]
          exact hunit q hq
        have hcount : FractionalIdeal.count K q
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) = 0 := by
          rw [IdeleClassGroup.count_spanSingleton_eq q (Units.ne_zero a), hval',
            WithZero.log_one, neg_zero]
        have hcomp : (((uUnitHom a (Place.ofFinite q) : (q.adicCompletion K)ˣ) :
              q.adicCompletion K))
            = (algebraMap K (q.adicCompletion K) (a : K))⁻¹ := by
          rw [uUnitHom_apply_ofFinite, hcount, zpow_zero, one_mul, Units.val_inv_eq_inv_val,
            Units.coe_map]
          with_unfolding_all rfl
        have hne : (algebraMap K (q.adicCompletion K) (a : K)) ≠ 0 := by
          intro h0
          have h1 : Valued.v (algebraMap K (q.adicCompletion K) (a : K)) = 1 := by
            rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq q (a : K),
              hval']
          rw [h0, Valuation.map_zero] at h1
          exact one_ne_zero h1.symm
        have hkey : (algebraMap K (q.adicCompletion K) (a : K))⁻¹ - 1
            = -((algebraMap K (q.adicCompletion K) (a : K) - 1)
                * (algebraMap K (q.adicCompletion K) (a : K))⁻¹) := by
          rw [sub_mul, one_mul, mul_inv_cancel₀ hne, neg_sub]
        have hvinv : Valued.v ((algebraMap K (q.adicCompletion K) (a : K))⁻¹) = 1 := by
          rw [Valuation.map_inv,
            Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq q (a : K), hval',
            inv_one]
        show Valued.v ((((uUnitHom a (Place.ofFinite q) : (q.adicCompletion K)ˣ) :
            q.adicCompletion K)) - 1) ≤ WithZero.exp (-(𝔪.exps q : ℤ))
        calc Valued.v ((((uUnitHom a (Place.ofFinite q) : (q.adicCompletion K)ˣ) :
                q.adicCompletion K)) - 1)
            = Valued.v ((algebraMap K (q.adicCompletion K) (a : K))⁻¹ - 1) := by rw [hcomp]
          _ = Valued.v ((algebraMap K (q.adicCompletion K) (a : K) - 1)
                * (algebraMap K (q.adicCompletion K) (a : K))⁻¹) := by
                rw [hkey, Valuation.map_neg]
          _ = Valued.v (algebraMap K (q.adicCompletion K) (a : K) - 1)
                * Valued.v ((algebraMap K (q.adicCompletion K) (a : K))⁻¹) := by
                rw [Valuation.map_mul]
          _ = Valued.v (algebraMap K (q.adicCompletion K) (a : K) - 1) := by
                rw [hvinv, mul_one]
          _ = Valued.v (algebraMap K (q.adicCompletion K) (α - 1)) := by
                rw [ha, RingHom.map_sub, RingHom.map_one]
          _ ≤ WithZero.exp (-(𝔪.exps q : ℤ)) := hcong q hq
  · intro w hw hwpos
    have h1 : (((uUnitHom a (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion))
        = (algebraMap K w.Completion (a : K))⁻¹ := by
      rw [uUnitHom_apply_ofInfinite, Units.val_inv_eq_inv_val, Units.coe_map]
      with_unfolding_all rfl
    rw [h1, ha, map_inv₀]
    exact inv_pos.mpr (hpos w hw hwpos)

/-- Conversely, if the unit part of the idèle of `(β)` lies in `U(𝔪)` and `β` is a unit modulo
the support of `𝔪`, then `β⁻¹` satisfies `IsCongElem`. -/
theorem isCongElem_inv_of_mem_congSubgroup {𝔪 : NK.NUV2.RouteB.Modulus K} (β : Kˣ)
    (hcount : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
      FractionalIdeal.count K q (FractionalIdeal.spanSingleton (𝓞 K)⁰ (β : K)) = 0)
    (hβ : uUnitHom β ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪) :
    NK.NUV2.RouteB.IsCongElem K 𝔪 (((β⁻¹ : Kˣ) : K)) := by
  rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff] at hβ
  obtain ⟨hfin, hpos⟩ := hβ
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨-, hcong⟩ := hfin q
    rw [NK.NUV2.RouteB.IsCongAt] at hcong
    have hcomp : (((uUnitHom β (Place.ofFinite q) : (q.adicCompletion K)ˣ) :
          q.adicCompletion K)) = (algebraMap K (q.adicCompletion K) (β : K))⁻¹ := by
      rw [uUnitHom_apply_ofFinite, hcount q hq, zpow_zero, one_mul, Units.val_inv_eq_inv_val,
        Units.coe_map]
      with_unfolding_all rfl
    rw [hcomp] at hcong
    simpa only [Units.val_inv_eq_inv_val, map_inv₀, map_sub, map_one] using hcong
  · intro w hw hwpos
    have hthis := hpos w hw hwpos
    have h1 : (((uUnitHom β (Place.ofInfinite w) : (w.Completion)ˣ) : w.Completion))
        = (algebraMap K w.Completion (β : K))⁻¹ := by
      rw [uUnitHom_apply_ofInfinite, Units.val_inv_eq_inv_val, Units.coe_map]
      with_unfolding_all rfl
    rw [h1] at hthis
    simpa only [Units.val_inv_eq_inv_val, map_inv₀] using hthis

theorem classOfIdeal_eq_iff (K : Type) [Field K] [NumberField K] (𝔪 : NK.NUV2.RouteB.Modulus K)
    (I J : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hIcop : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ I)
    (hJcop : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ J) :
    NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I =
        NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) J ↔
      ∃ α : K, α ≠ 0 ∧ NK.NUV2.RouteB.IsCongElem K 𝔪 α ∧
        (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
          (J : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) α := by
  classical
  set U : Subgroup (Idele K) := NK.NUV2.RouteB.CongSubgroup K 𝔪 with hU_def
  have hI' : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hI
  have hJ' : (J : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have hcountI : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
      FractionalIdeal.count K q (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    intro q hq
    by_contra h
    exact hIcop q hq ((NK.HeckeL.Basic.IdealProdFinsupp.count_coe_ne_zero_iff_dvd hI q).mp h)
  have hcountJ : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
      FractionalIdeal.count K q (J : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    intro q hq
    by_contra h
    exact hJcop q hq ((NK.HeckeL.Basic.IdealProdFinsupp.count_coe_ne_zero_iff_dvd hJ q).mp h)
  constructor
  · intro hmk
    have hmk' : (QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K I) :
          Idele K ⧸ (Idele.principalSubgroup K ⊔ U))
        = (QuotientGroup.mk (NK.HeckeL.ideleOfIdeal K J) :
          Idele K ⧸ (Idele.principalSubgroup K ⊔ U)) := by
      rw [← classOfIdeal_eq_mk (K := K) U I, ← classOfIdeal_eq_mk (K := K) U J]
      exact hmk
    have hmem : (NK.HeckeL.ideleOfIdeal K I)⁻¹ * NK.HeckeL.ideleOfIdeal K J
        ∈ Idele.principalSubgroup K ⊔ U :=
      (QuotientGroup.eq (s := Idele.principalSubgroup K ⊔ U)).mp hmk'
    obtain ⟨p, hp, u, hu, hpu⟩ := Subgroup.mem_sup.mp hmem
    obtain ⟨β, hβ⟩ := Idele.mem_principalSubgroup.mp hp
    have huInt : u ∈ Idele.integralIdeles K := by
      rw [Idele.mem_integralIdeles]
      intro v hv
      rw [Place.isFinite_iff] at hv
      obtain ⟨q, rfl⟩ := hv
      rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
      rw [hU_def] at hu
      rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff] at hu
      exact (hu.1 q).1
    have hxIdeal : Idele.idealOf (NK.HeckeL.ideleOfIdeal K I)
        = (I : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [ideleOfIdeal_eq_ideleOfFracK]
      exact idealOf_ideleOfFracK hI'
    have hxJdeal : Idele.idealOf (NK.HeckeL.ideleOfIdeal K J)
        = (J : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [ideleOfIdeal_eq_ideleOfFracK]
      exact idealOf_ideleOfFracK hJ'
    have hL : Idele.idealOf (p * u) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (β : K) := by
      rw [Idele.idealOf_mul, ← hβ, Idele.idealOf_principalIdele,
        (Idele.idealOf_eq_one_iff u).mpr huInt, mul_one]
    have hR : Idele.idealOf ((NK.HeckeL.ideleOfIdeal K I)⁻¹ * NK.HeckeL.ideleOfIdeal K J)
        = (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * (J : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [Idele.idealOf_mul, Idele.idealOf_inv, hxIdeal, hxJdeal]
    have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (β : K)
        = (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * (J : FractionalIdeal (𝓞 K)⁰ K) :=
      hL.symm.trans ((congrArg Idele.idealOf hpu).trans hR)
    have hu_eq : u = uUnitHom β := by
      have h1 : u = p⁻¹ * ((NK.HeckeL.ideleOfIdeal K I)⁻¹ * NK.HeckeL.ideleOfIdeal K J) := by
        rw [← hpu]; group
      rw [h1, ← hβ, ideleOfIdeal_eq_ideleOfFracK, ideleOfIdeal_eq_ideleOfFracK]
      rw [← ideleOfFracK_inv hI', ← ideleOfFracK_mul (inv_ne_zero hI') hJ', ← hspan,
        ideleOfFracK_spanSingleton_eq β]
      group
    have hmemU : uUnitHom β ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
      rw [← hu_eq]
      rw [hU_def] at hu
      exact hu
    have hJI : (J : FractionalIdeal (𝓞 K)⁰ K)
        = (I : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (β : K) := by
      rw [hspan, ← mul_assoc, mul_inv_cancel₀ hI', one_mul]
    have hS : FractionalIdeal.spanSingleton (𝓞 K)⁰ (β : K) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero β)
    refine ⟨((β⁻¹ : Kˣ) : K), Units.ne_zero _, ?_, ?_⟩
    · refine isCongElem_inv_of_mem_congSubgroup β ?_ hmemU
      intro q hq
      rw [hspan, FractionalIdeal.count_mul K q (inv_ne_zero hI') hJ', FractionalIdeal.count_inv,
        hcountI q hq, hcountJ q hq]
      simp
    · rw [Units.val_inv_eq_inv_val β]
      have hSinv : (FractionalIdeal.spanSingleton (𝓞 K)⁰ (β : K))⁻¹
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ ((β : K)⁻¹) :=
        FractionalIdeal.spanSingleton_inv K (β : K)
      rw [← hSinv, hJI, mul_assoc, mul_inv_cancel₀ hS, mul_one]
  · rintro ⟨α, hα, hcong, heq⟩
    set a : Kˣ := Units.mk0 α hα with ha_def
    have ha : (a : K) = α := by rw [ha_def]; exact Units.val_mk0 hα
    have hsp_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ α ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hα
    have hunit : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
        Valued.v (algebraMap K (q.adicCompletion K) α) = 1 := by
      intro q hq
      have h := hcountI q hq
      rw [heq, FractionalIdeal.count_mul K q hJ' hsp_ne, hcountJ q hq, zero_add,
        IdeleClassGroup.count_spanSingleton_eq q hα, neg_eq_zero] at h
      have hne : (HeightOneSpectrum.valuation K q) α ≠ 0 :=
        (Valuation.ne_zero_iff (HeightOneSpectrum.valuation K q)).mpr hα
      have hval1 : (HeightOneSpectrum.valuation K q) α = 1 := by
        rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
      rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq q α, hval1]
    have hmemU : uUnitHom a ∈ U := by
      rw [hU_def, ha_def]
      exact uUnitHom_mem_congSubgroup hα hunit hcong
    have heq' : (I : FractionalIdeal (𝓞 K)⁰ K)
        = (J : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) := by
      rw [heq, ha]
    have hid : NK.HeckeL.ideleOfIdeal K I
        = NK.HeckeL.ideleOfIdeal K J * Idele.principalIdele K a * uUnitHom a := by
      rw [ideleOfIdeal_eq_ideleOfFracK, ideleOfIdeal_eq_ideleOfFracK, heq',
        ideleOfFracK_mul hJ'
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero a)),
        ideleOfFracK_spanSingleton_eq a, mul_assoc]
    rw [classOfIdeal_eq_mk, classOfIdeal_eq_mk, hid]
    refine (QuotientGroup.eq (s := Idele.principalSubgroup K ⊔ U)).mpr ?_
    have hkey : (NK.HeckeL.ideleOfIdeal K J * Idele.principalIdele K a * uUnitHom a)⁻¹
        * NK.HeckeL.ideleOfIdeal K J
        = (uUnitHom a)⁻¹ * (Idele.principalIdele K a)⁻¹ := by group
    rw [hkey]
    exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right (show uUnitHom a ∈ U from hmemU)))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left ⟨a, rfl⟩))

end NK.NUV2.RouteB.RayModulus
