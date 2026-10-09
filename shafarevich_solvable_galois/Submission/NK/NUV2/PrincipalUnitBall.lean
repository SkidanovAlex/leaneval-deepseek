import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_adicCompletion_iff
import Submission.Commons.NumberTheory.NumberField.Completion.finite_adicCompletionIntegers_quotient_maximalIdeal_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `M`-th principal-unit ball of the integers of a `q`-adic completion

For a number field `K`, a finite prime `q` and `M : ℕ`, the *`M`-th principal unit group* of
`R = 𝓞_{K_q}` is the kernel of the reduction `Rˣ → (R/𝔪^M)ˣ`:

`principalUnitBall K q M = {u : Rˣ | (u : R) - 1 ∈ 𝔪^M} = {u : Rˣ | v (u - 1) ≤ exp (-M)}`,

where `v = Valued.v` is the (discrete) valuation of the completion `K_q` (the equality of the two
descriptions is `Commons.…val_le_exp_neg_iff_mem_maximalIdeal_pow`).

This is the group `1 + 𝔪^M` whose `ℤ_2`-dual is bounded by `e·f = [K_q : ℚ_2]` in
`NK.NUV2.localUnits_two`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField WithZero

namespace NK.NUV2

open IsDedekindDomain

/-- **The `M`-th principal unit group** `1 + 𝔪^M` of the ring of integers of the `q`-adic
completion, as the kernel of the reduction modulo `𝔪^M` on units. -/
noncomputable def principalUnitBall (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (M : ℕ) :
    Subgroup (q.adicCompletionIntegers K)ˣ :=
  (Units.map (Ideal.Quotient.mk
    (IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M)).toMonoidHom).ker

/-- Membership in the `M`-th principal unit group, in terms of the maximal ideal. -/
theorem mem_principalUnitBall_iff {K : Type} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (M : ℕ)
    (u : (q.adicCompletionIntegers K)ˣ) :
    u ∈ principalUnitBall K q M ↔
      ((u : q.adicCompletionIntegers K) - 1) ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M := by
  let I : Ideal (q.adicCompletionIntegers K) :=
    IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M
  have hkey : u ∈ principalUnitBall K q M ↔
      (Ideal.Quotient.mk I : q.adicCompletionIntegers K →+*
        q.adicCompletionIntegers K ⧸ I) ((u : q.adicCompletionIntegers K) - 1) = 0 := by
    rw [principalUnitBall, MonoidHom.mem_ker]
    constructor
    · intro h
      have hh : (Ideal.Quotient.mk I : q.adicCompletionIntegers K →+*
          q.adicCompletionIntegers K ⧸ I) ((u : q.adicCompletionIntegers K)) = 1 := by
        have h2 := Units.ext_iff.mp h
        simpa [Units.coe_map] using h2
      rw [map_sub, hh, map_one, sub_self]
    · intro h
      rw [Units.ext_iff]
      rw [Units.coe_map, Units.val_one]
      have h3 : (Ideal.Quotient.mk I : q.adicCompletionIntegers K →+*
          q.adicCompletionIntegers K ⧸ I) ((u : q.adicCompletionIntegers K) - 1) = 0 := h
      rw [map_sub, map_one] at h3
      exact sub_eq_zero.mp h3
  rw [hkey]
  exact (Ideal.Quotient.eq_zero_iff_mem (I := I))

/-- Membership in the `M`-th principal unit group, in terms of the valuation of the completion:
`v (u - 1) ≤ exp (-M)`. -/
theorem mem_principalUnitBall_iff_val {K : Type} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (M : ℕ)
    (u : (q.adicCompletionIntegers K)ˣ) :
    u ∈ principalUnitBall K q M ↔
      Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((u : q.adicCompletionIntegers K) : q.adicCompletion K) - 1) ≤
        (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) := by
  rw [mem_principalUnitBall_iff]
  exact (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
    q ((u : q.adicCompletionIntegers K) - 1) M).symm

end NK.NUV2

namespace NK.NUV2

/-- **The `M`-th principal unit group has finite index in the units of `𝓞_{K_q}`.**  Its quotient
`(𝓞_{K_q}/𝔪^M)ˣ` is the group of units of the finite local ring `𝓞_{K_q}/𝔪^M`. -/
theorem principalUnitBall_finiteIndex (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (M : ℕ) :
    (principalUnitBall K q M).FiniteIndex := by
  haveI : Finite (q.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M) :=
    Commons.NumberTheory.NumberField.Completion.finite_adicCompletionIntegers_quotient_maximalIdeal_pow
      K q M
  haveI : Finite ((q.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M))ˣ := inferInstance
  rw [principalUnitBall]
  refine Subgroup.FiniteIndex.mk ?_
  rw [Subgroup.index_ker]
  exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

end NK.NUV2
