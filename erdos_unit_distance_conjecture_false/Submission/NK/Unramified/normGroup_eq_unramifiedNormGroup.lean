import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Basic
import Submission.NK.LocalReciprocity.NormGroup
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial

/-!
# The norm group of an unramified local extension is `⟨π^m⟩ · U^0`

For a finite Galois extension of number fields `L / K`, a place `Q` of `K` and a place `Q'` of `L`
above it with **ramification index one**, the local extension `L_{Q'} / K_Q` of completions is
unramified of degree `m = [L_{Q'} : K_Q] = f(Q'/Q)`, and its norm group on units is the group

  `N_{L_{Q'}/K_Q} L_{Q'}ˣ = ⟨π^m⟩ · U^0`,

where `π` is a uniformiser of `K_Q` and `U^0 = 𝒪_{K_Q}ˣ` is the group of units of the ring of
integers.  This is the unramified case of the local norm group computation: the norm map is
surjective on units (`Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one`,
equivalently the explicit computation `norm_range_of_ramificationIdx_eq_one`) and a uniformiser
of `L_{Q'}` has norm a uniformiser of `K_Q`, so on `π^ℤ` the norm acts as multiplication by `m`.

## Formalisation

The statement is the identity of the two subgroups of `(K_Q)ˣ`:

* `NK.LocalReciprocity.normGroup (Q.adicCompletion K) (Q'.adicCompletion L)` — the image of the
  norm map on units (`NK.LocalReciprocity.normGroup`), and
* `NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q m = ⟨π^m⟩ · U^0` (the `m`-th unramified
  level's norm group, `NK.LocalReciprocityLubinTate/Unramified/Basic.lean`).

The proof goes through the `ℤ`-valued logarithm of the valuation,
`Commons.NumberTheory.NumberField.Completion.unitsValLog : (K_Q)ˣ →* Multiplicative ℤ`: both sides
are the preimage of the subgroup of `m`-th powers of `Multiplicative ℤ` under `unitsValLog`, the
norm-group side by `unitsValLog_norm`, and the right-hand side because
`unitsValLog (π^m) = (unitsValLog π)^m` and `adicUnits K Q = ker unitsValLog`.
-/

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace NK.Unramified

noncomputable section

namespace NormGroupEqUnramified

variable {K : Type} [Field K] [NumberField K]
  (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

local notation "nu" => Commons.NumberTheory.NumberField.Completion.unitsValLog (Q.adicCompletion K)
local notation "vv" => Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
local notation "pi" => NK.LocalReciprocityLubinTate.uniformizerUnit K Q
local notation "A" => NK.LocalReciprocityLubinTate.adicUnits K Q

/-- The uniformiser of the completion, as an element of the completion, has value
`WithZero.exp (-1)`. -/
theorem val_uniformizerUnit : vv (pi : Q.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  rw [NK.LocalReciprocityLubinTate.uniformizerUnit, Units.val_mk0]
  exact Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q

/-- The value-logarithm of the uniformiser is `-1`. -/
theorem unitsValLog_uniformizerUnit :
    nu pi = Multiplicative.ofAdd (-1 : ℤ) := by
  rw [Commons.NumberTheory.NumberField.Completion.unitsValLog_apply, val_uniformizerUnit Q,
    WithZero.log_exp]

/-- `(g^m)^k = (g^k)^m` in a group. -/
theorem pow_zpow_comm {G : Type*} [Group G] (g : G) (m : ℕ) (k : ℤ) :
    (g ^ m) ^ k = (g ^ k) ^ m := by
  rw [← zpow_natCast g m, ← zpow_natCast (g ^ k) m]
  rw [← zpow_mul, ← zpow_mul, mul_comm]

/-- `adicUnits K Q` is the unit group of the ring of integers of the completion. -/
theorem adicUnits_eq_unitGroup :
    A = (Q.adicCompletionIntegers K).unitGroup := by
  rw [NK.LocalReciprocityLubinTate.adicUnits, ← MonoidHom.range_eq_map]
  refine le_antisymm ?_ ?_
  · rintro u ⟨w, rfl⟩
    change Units.map (Q.adicCompletionIntegers K).subtype.toMonoidHom w ∈
      (Q.adicCompletionIntegers K).unitGroup
    change ((ValuationSubring.unitGroupMulEquiv (Q.adicCompletionIntegers K)).symm w :
      (Q.adicCompletion K)ˣ) ∈ (Q.adicCompletionIntegers K).unitGroup
    exact ((ValuationSubring.unitGroupMulEquiv (Q.adicCompletionIntegers K)).symm w).2
  · intro u hu
    refine ⟨(Q.adicCompletionIntegers K).unitGroupMulEquiv ⟨u, hu⟩, ?_⟩
    apply Units.ext
    rw [Units.coe_map]
    change ((Q.adicCompletionIntegers K).unitGroupMulEquiv ⟨u, hu⟩ : Q.adicCompletion K)
      = (u : Q.adicCompletion K)
    rfl

/-- **Membership in `U^0`**: the units of the ring of integers are exactly the units of
valuation one. -/
theorem mem_adicUnits_iff (x : (Q.adicCompletion K)ˣ) :
    x ∈ A ↔ vv (x : Q.adicCompletion K) = 1 := by
  rw [adicUnits_eq_unitGroup Q]
  change x ∈ (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))).valuationSubring.unitGroup ↔ _
  rw [Valuation.mem_unitGroup_iff]

/-- The value-logarithm controls the valuation on `m`-th powers: if `nu x = (nu w)^m` then
`v x = (v w)^m`. -/
theorem val_pow_of_unitsValLog_pow (x w : (Q.adicCompletion K)ˣ) (m : ℕ)
    (h : nu x = (nu w) ^ m) :
    vv (x : Q.adicCompletion K) = (vv (w : Q.adicCompletion K)) ^ m := by
  have hx0 : vv (x : Q.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff vv).mpr (Units.ne_zero x)
  have hw0 : vv (w : Q.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff vv).mpr (Units.ne_zero w)
  have h1 := congrArg Multiplicative.toAdd h
  rw [Int.toAdd_pow, Commons.NumberTheory.NumberField.Completion.unitsValLog_apply,
    Commons.NumberTheory.NumberField.Completion.unitsValLog_apply, toAdd_ofAdd,
    toAdd_ofAdd] at h1
  rw [← WithZero.exp_log hx0, ← WithZero.exp_log hw0, ← WithZero.exp_nsmul, h1]
  congr 1
  rw [nsmul_eq_mul, mul_comm]

/-- **Membership in the unramified norm group** `⟨π^m⟩ · U^0`: an element of `(K_Q)ˣ` lies in
`⟨π^m⟩ · U^0` exactly when its value-logarithm is an `m`-th power. -/
theorem mem_unramifiedNormGroup_iff (m : ℕ) (x : (Q.adicCompletion K)ˣ) :
    x ∈ NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q m
      ↔ ∃ w : (Q.adicCompletion K)ˣ, nu x = (nu w) ^ m := by
  unfold NK.LocalReciprocityLubinTate.unramifiedNormGroup
  constructor
  · intro hx
    rw [Subgroup.mem_sup] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    rw [Subgroup.mem_zpowers_iff] at ha
    obtain ⟨k, rfl⟩ := ha
    have hb1 : nu b = 1 := by
      rw [Commons.NumberTheory.NumberField.Completion.unitsValLog_eq_one_iff]
      exact (mem_adicUnits_iff Q b).mp hb
    refine ⟨pi ^ k, ?_⟩
    rw [← hab, map_mul, hb1, mul_one, map_zpow, map_pow, map_zpow]
    simp only [unitsValLog_uniformizerUnit Q]
    exact pow_zpow_comm (Multiplicative.ofAdd (-1 : ℤ)) m k
  · rintro ⟨w, hw⟩
    set k : ℤ := (nu w).toAdd with hk
    have hwk : nu w = Multiplicative.ofAdd k := by
      rw [hk]; exact (ofAdd_toAdd _).symm
    have hxnu : nu x = Multiplicative.ofAdd (k * ↑m) := by
      have h' : (nu w) ^ m = Multiplicative.ofAdd (k * ↑m) := by
        rw [hwk]
        apply Multiplicative.toAdd.injective
        rw [Int.toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
      rw [hw, h']
    have hnu_a : nu ((pi ^ m) ^ (-k)) = Multiplicative.ofAdd (k * ↑m) := by
      rw [map_zpow, map_pow, unitsValLog_uniformizerUnit Q]
      apply Multiplicative.toAdd.injective
      simp only [Int.toAdd_zpow, Int.toAdd_pow, toAdd_ofAdd]
      ring
    have hb1 : nu (x * ((pi ^ m) ^ (-k))⁻¹) = 1 := by
      rw [map_mul, map_inv, hxnu, hnu_a]
      simp
    have hb : (x * ((pi ^ m) ^ (-k))⁻¹) ∈ A := by
      rw [mem_adicUnits_iff Q]
      rw [← Commons.NumberTheory.NumberField.Completion.unitsValLog_eq_one_iff]
      exact hb1
    refine Subgroup.mem_sup.mpr ⟨(pi ^ m) ^ (-k), ?_, x * ((pi ^ m) ^ (-k))⁻¹, hb, ?_⟩
    · rw [Subgroup.mem_zpowers_iff]; exact ⟨-k, rfl⟩
    · rw [← mul_assoc, mul_comm ((pi ^ m) ^ (-k)) x, mul_assoc]
      simp

variable {L : Type*} [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Membership in the local norm group of an unramified extension**: `x` is a norm from
`L_{Q'}` if and only if its value-logarithm is an `f(Q'/Q)`-th power. -/
theorem mem_normGroup_iff
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (Q' : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (h : Q'.asIdeal.LiesOver Q.asIdeal)
    (hunr : Q'.asIdeal.ramificationIdx (𝓞 K) = 1)
    (x : (Q.adicCompletion K)ˣ) :
    letI : Algebra (Q.adicCompletion K) (Q'.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q Q' h)
    x ∈ NK.LocalReciprocity.normGroup (Q.adicCompletion K) (Q'.adicCompletion L) ↔
      ∃ w : (Q.adicCompletion K)ˣ,
        Commons.NumberTheory.NumberField.Completion.unitsValLog (Q.adicCompletion K) x =
          (Commons.NumberTheory.NumberField.Completion.unitsValLog (Q.adicCompletion K) w)
            ^ (Q'.asIdeal.inertiaDeg (𝓞 K)) := by
  letI : Algebra (Q.adicCompletion K) (Q'.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q Q' h)
  haveI : FiniteDimensional (Q.adicCompletion K) (Q'.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q Q' h
  constructor
  · intro hx
    rw [NK.LocalReciprocity.mem_normGroup_iff] at hx
    obtain ⟨u, hu⟩ := hx
    have hxmu : Units.map (Algebra.norm (Q.adicCompletion K) :
        (Q'.adicCompletion L) →* (Q.adicCompletion K)) u = x := Units.ext hu
    obtain ⟨w, hw⟩ := Commons.NumberTheory.NumberField.Completion.unitsValLog_adicCompletion_surjective
      K Q (Commons.NumberTheory.NumberField.Completion.unitsValLog (Q'.adicCompletion L) u)
    refine ⟨w, ?_⟩
    rw [← hxmu, Commons.NumberTheory.NumberField.Completion.unitsValLog_norm Q Q' h u, hw]
  · rintro ⟨w, hw⟩
    rw [NK.LocalReciprocity.mem_normGroup_iff]
    have hval := val_pow_of_unitsValLog_pow Q x w (Q'.asIdeal.inertiaDeg (𝓞 K)) hw
    obtain ⟨y, hy⟩ := (Commons.NumberTheory.NumberField.Completion.norm_range_of_ramificationIdx_eq_one
      Q Q' h hunr (x : Q.adicCompletion K)).mpr ⟨(w : Q.adicCompletion K), hval⟩
    haveI : Module.Free (Q.adicCompletion K) (Q'.adicCompletion L) :=
      Module.Free.of_divisionRing _ _
    have hyne : y ≠ 0 := by
      intro h0
      rw [h0, Algebra.norm_zero] at hy
      exact (Units.ne_zero x) hy.symm
    exact ⟨Units.mk0 y hyne, by rw [Units.val_mk0]; exact hy⟩

end NormGroupEqUnramified

theorem normGroup_eq_unramifiedNormGroup {K : Type} [Field K] [NumberField K]
    {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : Q'.asIdeal.LiesOver Q.asIdeal)
    (hunr : Q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (Q'.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q Q' h)
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) (Q'.adicCompletion L)
      = NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q
        (Q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  letI : Algebra (Q.adicCompletion K) (Q'.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q Q' h)
  refine Subgroup.ext (fun x => ?_)
  rw [NormGroupEqUnramified.mem_normGroup_iff Q Q' h hunr x,
    NormGroupEqUnramified.mem_unramifiedNormGroup_iff Q (Q'.asIdeal.inertiaDeg (𝓞 K)) x]

end

end NK.Unramified
