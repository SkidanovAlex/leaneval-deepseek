import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.NUV2.LC.hilbertReciprocity
import Submission.NK.Unramified.normGroup_eq_unramifiedNormGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm group of an unramified local extension, in terms of the valuation

For a finite Galois extension `L / K` of number fields, a finite place `Q` of `K` and a place `q`
of `L` above it with **ramification index one**, the local extension `L_q / K_Q` is unramified with
inertia degree `f = f(q/Q)`, and its norm group on units is

  `N_{L_q/K_Q} L_qˣ = 𝒪_{K_Q}ˣ · π^{fℤ}`.

Equivalently: `x` is a local norm if and only if its valuation is an `f`-th power in the value
group `ℤᵐ⁰` — which is the statement proved here.  The input is the existing computation
`NK.Unramified.normGroup_eq_unramifiedNormGroup` (the norm group in terms of the ℤ-valued
logarithm of the valuation), transported to `Valued.v` along
`unitsValLog F x = Multiplicative.ofAdd ((Valued.v x).log)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped NumberField WithZero
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

namespace NK.NUV2.LC

/-- **The logarithm of the valuation detects powers**: for units `x y` of a valued field, `x` has
the same value-logarithm as an `n`-th power of the value-logarithm of `y` if and only if
`v x = (v y)ⁿ`. -/
theorem unitsValLog_pow_iff {F : Type*} [Field F] [Valued F (WithZero (Multiplicative ℤ))]
    (x y : Fˣ) (n : ℕ) :
    Commons.NumberTheory.NumberField.Completion.unitsValLog F x =
        (Commons.NumberTheory.NumberField.Completion.unitsValLog F y) ^ n ↔
      Valued.v (x : F) = (Valued.v (y : F)) ^ n := by
  have hx : Valued.v (R := F) (x : F) ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v (R := F))).mpr (Units.ne_zero x)
  have hy : Valued.v (R := F) (y : F) ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v (R := F))).mpr (Units.ne_zero y)
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    rw [Commons.NumberTheory.NumberField.Completion.unitsValLog_apply,
      Commons.NumberTheory.NumberField.Completion.unitsValLog_apply, toAdd_ofAdd, toAdd_pow,
      toAdd_ofAdd] at h'
    rw [← WithZero.exp_log hx, ← WithZero.exp_log hy, h', WithZero.exp_nsmul]
  · intro h
    rw [Commons.NumberTheory.NumberField.Completion.unitsValLog_apply,
      Commons.NumberTheory.NumberField.Completion.unitsValLog_apply, h, WithZero.log_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]

/-- **The local norm group of an unramified local extension, in terms of `Valued.v`.** -/
theorem localNormFinite_range_iff_val_pow {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) (x : (Q.adicCompletion K)ˣ) :
    x ∈ (NK.GlobalCFT.Place.localNormFinite q Q hq).range ↔
      ∃ y : (Q.adicCompletion K)ˣ,
        Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (x : Q.adicCompletion K) =
          (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (y : Q.adicCompletion K)) ^ (q.asIdeal.inertiaDeg (𝓞 K)) := by
  have hrange : (NK.GlobalCFT.Place.localNormFinite q Q hq).range =
      NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L) := by
    unfold NK.GlobalCFT.Place.localNormFinite NK.LocalReciprocity.normGroup
    rfl
  have hkey : x ∈ NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L) ↔
      ∃ w : (Q.adicCompletion K)ˣ,
        Commons.NumberTheory.NumberField.Completion.unitsValLog (Q.adicCompletion K) x =
          (Commons.NumberTheory.NumberField.Completion.unitsValLog (Q.adicCompletion K) w)
            ^ (q.asIdeal.inertiaDeg (𝓞 K)) :=
    NK.Unramified.NormGroupEqUnramified.mem_normGroup_iff Q q hq hunr x
  rw [hrange, hkey]
  exact exists_congr fun y => unitsValLog_pow_iff x y _

/-- **The same criterion, in the `localIncl` form used by `IsLocalNorm`.** -/
theorem localIncl_mem_range_localNormFinite_iff {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) (u : Kˣ) :
    localIncl K (NK.GlobalCFT.Place.ofFinite Q) u ∈
        (NK.GlobalCFT.Place.localNormFinite q Q hq).range ↔
      ∃ y : (Q.adicCompletion K)ˣ,
        Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap K (Q.adicCompletion K) (u : K)) =
          (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (y : Q.adicCompletion K)) ^ (q.asIdeal.inertiaDeg (𝓞 K)) := by
  show (Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom u) ∈
    (NK.GlobalCFT.Place.localNormFinite q Q hq).range ↔ _
  rw [localNormFinite_range_iff_val_pow Q q hq hunr]
  refine exists_congr fun y => ?_
  simp [Units.coe_map]

end NK.NUV2.LC
