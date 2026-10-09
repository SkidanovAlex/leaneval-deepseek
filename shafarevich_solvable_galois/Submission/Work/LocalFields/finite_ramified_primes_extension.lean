import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField

/-- A finite prime `w` of `L` that is ramified over `K` (i.e. whose inertia subgroup is
nontrivial) is also ramified over `ℤ`, i.e. the extension `𝓞 L / ℤ` is ramified at `w`.

Indeed, if `v` denotes the prime of `K` below `w`, multiplicativity of ramification indices in
the tower `ℤ ⊆ 𝓞 K ⊆ 𝓞 L` gives
`e(w/ℤ) = e(v/ℤ) · e(w/v)`,
and `e(w/v) = ramificationIdxIn v (𝓞 L) ≠ 1` by hypothesis (Galois case), so `e(w/ℤ) ≠ 1`. -/
theorem not_isUnramifiedAt_int_of_not_isUnramifiedAt {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : FinitePrime K) (w : FinitePrime L) [hw : w.asIdeal.LiesOver v.asIdeal]
    (h : ¬ IsUnramifiedAt K w) : ¬ Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  intro h2
  -- `w` is unramified over `ℤ`, hence `e(w/ℤ) = 1`.
  have h3 : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  -- Multiplicativity of ramification indices in the tower `ℤ ⊆ 𝓞 K ⊆ 𝓞 L`.
  have h4 : w.asIdeal.ramificationIdx ℤ =
      v.asIdeal.ramificationIdx ℤ * w.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_tower v.asIdeal w.asIdeal
  -- Hence `e(w/v) = 1`.
  have h5 : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [h4] at h3
    exact Nat.eq_one_of_mul_eq_one_left h3
  -- And in the Galois case `e(w/v) = ramificationIdxIn v (𝓞 L)`.
  have h6 : v.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (G := Gal(L/K)) v.asIdeal w.asIdeal]
    exact h5
  -- Contradiction with `¬ IsUnramifiedAt K w`.
  exact h ((isUnramifiedAt_iff_ramificationIdxIn_eq_one v w).mpr h6)

/-- **Only finitely many primes of `K` ramify in a finite Galois extension `L/K`.**

More precisely: the set of finite primes `v` of `K` for which *some* prime `w` of `L` above `v`
is ramified over `K` (i.e. has nontrivial inertia subgroup) is finite.

The proof reduces to the absolute statement for `L`: if `w` is ramified over `K` then it is
ramified over `ℤ` (`not_isUnramifiedAt_int_of_not_isUnramifiedAt`), and the primes of `L`
ramified over `ℤ` are exactly the prime divisors of the nonzero different ideal
`differentIdeal ℤ (𝓞 L)`, of which there are finitely many
(`Ideal.finite_factors`, via `dvd_differentIdeal_iff`).  Each such `w` determines the prime of
`K` below it, so the required set is contained in the image of a finite set. -/
theorem finite_ramified_primes_extension {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    {v : Work.LocalFields.FinitePrime K |
      ∃ w : Work.LocalFields.FinitePrime L,
        w.asIdeal.LiesOver v.asIdeal ∧ ¬ Work.LocalFields.IsUnramifiedAt K w}.Finite := by
  classical
  -- The primes `w` of `L` ramified over `ℤ` are the prime divisors of the (nonzero) different
  -- ideal of `𝓞 L / ℤ`, hence finite.
  have hW : {w : FinitePrime L | ¬ Algebra.IsUnramifiedAt ℤ w.asIdeal}.Finite := by
    have h : (differentIdeal ℤ (𝓞 L)) ≠ 0 := differentIdeal_ne_bot
    refine (Ideal.finite_factors h).subset ?_
    intro w hw
    exact dvd_differentIdeal_iff.mpr hw
  -- The prime of `K` lying below a prime of `L`.
  let f : FinitePrime L → FinitePrime K := fun w =>
    ⟨w.asIdeal.under (𝓞 K), Ideal.IsPrime.under _ _, Ideal.under_ne_bot _ w.ne_bot⟩
  refine (hW.image f).subset ?_
  rintro v ⟨w, hw_over, hw_unram⟩
  refine ⟨w, ?_, ?_⟩
  · -- `w` is ramified over `ℤ`, so it belongs to the finite set above.
    exact not_isUnramifiedAt_int_of_not_isUnramifiedAt v w hw_unram
  · -- `v` is the prime of `K` below `w`, i.e. `f w = v`.
    exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
      (Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal)).symm

end Work.LocalFields
