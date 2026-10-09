import Mathlib
import Submission.NK.HeckeL.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

namespace NK.HeckeL.Basic

/-- **Only finitely many primes ramify in a finite extension of number fields.**

The set of finite places `𝔭` of `K` at which the extension `L / K` is ramified is finite: it is
contained in the (finite) set of primes of `K` lying below a prime divisor of the relative
different `𝔇_{L/K}`, and a nonzero ideal of a Dedekind domain has only finitely many prime
divisors. -/
theorem finite_setOf_not_isUnramifiedIn {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    {𝔭 : NK.HeckeL.PrimeIdeal K | ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭}.Finite := by
  -- The relative different is a nonzero ideal of `𝓞 L`.
  have hdiff : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : {𝔮 : NK.HeckeL.PrimeIdeal L | 𝔮.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L)}.Finite :=
    Ideal.finite_factors hdiff
  -- A prime of `L` dividing the different maps to the prime of `K` below it.
  let f : NK.HeckeL.PrimeIdeal L → NK.HeckeL.PrimeIdeal K := fun 𝔮 =>
    ⟨𝔮.asIdeal.under (𝓞 K), Ideal.IsPrime.under _ _, by
      intro h
      rw [Ideal.under_def] at h
      exact 𝔮.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)⟩
  refine (hfin.image f).subset ?_
  rintro 𝔭 h𝔭
  -- `𝔭` ramified means some prime `𝔮` above it has ramification index `≠ 1`, hence `𝔮` is
  -- ramified in the sense of `Algebra.IsUnramifiedAt`, hence `𝔮 ∣ 𝔇`.
  simp only [NK.HeckeL.IsUnramifiedIn] at h𝔭
  push Not at h𝔭
  obtain ⟨𝔮, hlo, he⟩ := h𝔭
  refine ⟨𝔮, ?_, ?_⟩
  · change 𝔮.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L)
    rw [dvd_differentIdeal_iff]
    intro hunr
    exact he (Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K) (S := 𝓞 L))
  · exact IsDedekindDomain.HeightOneSpectrum.ext
      (Ideal.LiesOver.over (P := 𝔮.asIdeal) (p := 𝔭.asIdeal)).symm

end NK.HeckeL.Basic
