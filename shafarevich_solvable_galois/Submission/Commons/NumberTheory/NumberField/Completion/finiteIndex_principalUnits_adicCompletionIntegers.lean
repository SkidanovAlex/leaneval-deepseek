import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.finite_adicCompletionIntegers_quotient_maximalIdeal_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

/-- For a commutative ring `R`, an ideal `I` and a unit `u : Rˣ`, the unit `u` lies in the kernel
of the reduction map `Rˣ → (R ⧸ I)ˣ` if and only if `u - 1 ∈ I`, i.e. `u ≡ 1 (mod I)`. -/
theorem mem_ker_units_idealQuotientMk_iff {R : Type*} [CommRing R] (I : Ideal R) (u : Rˣ) :
    u ∈ (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker ↔ ((u : R) - 1) ∈ I := by
  rw [MonoidHom.mem_ker, ← Units.val_eq_one, Units.coe_map]
  exact Ideal.Quotient.mk_eq_one_iff_sub_mem (u : R)

/-- **The `C`-th principal unit group of the `v`-adic completion of a number field has finite
index in the full unit group.**

For a number field `K`, a finite place `v` of `K` and `C : ℕ`, the set of units `u` of the ring of
integers `𝓞_v = v.adicCompletionIntegers K` of the `v`-adic completion with `u ≡ 1 (mod 𝔪^C)`
forms a subgroup `U` and `U` has finite index in `𝓞_vˣ`.

Indeed `U` is the kernel of the reduction `𝓞_vˣ → (𝓞_v ⧸ 𝔪^C)ˣ`, and the target is finite because
`𝓞_v ⧸ 𝔪^C` is finite (`finite_adicCompletionIntegers_quotient_maximalIdeal_pow`). -/
theorem finiteIndex_principalUnits_adicCompletionIntegers {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (C : ℕ) :
    ∃ U : Subgroup (v.adicCompletionIntegers K)ˣ,
      (∀ u : (v.adicCompletionIntegers K)ˣ,
        u ∈ U ↔ ((u : v.adicCompletionIntegers K) - 1) ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ C) ∧
      U.FiniteIndex := by
  let R := v.adicCompletionIntegers K
  let I : Ideal R := IsLocalRing.maximalIdeal R ^ C
  haveI hfin : Finite (R ⧸ I) :=
    finite_adicCompletionIntegers_quotient_maximalIdeal_pow K v C
  let f : Rˣ →* (R ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom
  refine ⟨f.ker, ?_, ?_⟩
  · intro u
    exact mem_ker_units_idealQuotientMk_iff I u
  · haveI : Finite f.range := inferInstance
    exact Subgroup.finiteIndex_ker f

end Commons.NumberTheory.NumberField.Completion
