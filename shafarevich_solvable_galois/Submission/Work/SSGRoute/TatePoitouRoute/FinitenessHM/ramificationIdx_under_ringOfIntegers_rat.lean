import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.ratPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- The statement of the main theorem carries hypotheses (`hp`, `h0`, `hlies`) that the base-change
-- identity does not need; silence the corresponding linters rather than alter the statement.
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open Ideal

/-! ## Base change along `ℤ → 𝓞 ℚ`

`Ideal.ramificationIdx q R` is the length of `Localization.AtPrime q ⧸ (q.under R).map _`.  Hence an
identity of ramification indices over two different base rings only requires the two base changes of
`q.under R` into the localisation to agree.  For the base pair `ℤ` and `𝓞 ℚ` this is a formal
consequence of the scalar tower `ℤ → 𝓞 ℚ → 𝓞 K` together with the fact that `ℤ → 𝓞 ℚ` is an
isomorphism (its inverse being `Rat.ringOfIntegersEquiv`). -/

/-- The canonical algebra map `ℤ → 𝓞 ℚ` is the inverse of `Rat.ringOfIntegersEquiv`. -/
lemma algebraMap_int_ringOfIntegers_rat :
    (algebraMap ℤ (NumberField.RingOfIntegers ℚ)) = Rat.ringOfIntegersEquiv.symm := by
  ext x
  simp

/-- **Base change of `under` along `ℤ → 𝓞 ℚ`.**  For an ideal `P` of `𝓞 K`, the two ideals of
`Localization.AtPrime P` obtained by mapping `P.under ℤ` and `P.under (𝓞 ℚ)` into the localisation
coincide.  These are exactly the ideals whose lengths define the ramification indices of `P` over
the two base rings. -/
lemma map_under_eq_map_under_ringOfIntegers_rat
    {K : Type*} [Field K] [NumberField K] (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime] :
    (P.under ℤ).map (algebraMap ℤ (Localization.AtPrime P))
      = (P.under (NumberField.RingOfIntegers ℚ)).map
          (algebraMap (NumberField.RingOfIntegers ℚ) (Localization.AtPrime P)) := by
  -- Rewrite the `ℤ`-base change as base change to `𝓞 ℚ` followed by base change to the localisation.
  rw [IsScalarTower.algebraMap_eq ℤ (NumberField.RingOfIntegers ℚ) (Localization.AtPrime P),
    ← Ideal.map_map]
  congr 1
  -- It remains to identify `(P.under ℤ).map (algebraMap ℤ (𝓞 ℚ))` with `P.under (𝓞 ℚ)`.
  rw [Ideal.under_def ℤ P, Ideal.under_def (NumberField.RingOfIntegers ℚ) P,
    IsScalarTower.algebraMap_eq ℤ (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K),
    ← Ideal.comap_comap]
  -- `algebraMap ℤ (𝓞 ℚ)` is bijective, so `comap` followed by `map` returns the original ideal.
  exact Ideal.map_comap_of_surjective _
    (by rw [algebraMap_int_ringOfIntegers_rat]; exact Rat.ringOfIntegersEquiv.symm.surjective) _

/-- **Base-change glue.**  For a prime `P` of `𝓞 K` over `(p) ⊆ ℤ`, the ramification index of `P`
computed over the base `ℤ` equals the one computed over the base `𝓞 ℚ` (the two base rings being
canonically isomorphic and the relevant scalar towers compatible).  Needed because the local
statements about `p`-adic completions are phrased with the prime of `𝓞 ℚ`, while the target
`differentIdeal_count_le_proved` uses `P.ramificationIdx ℤ`.

Proof route (validated): `Ideal.ramificationIdx` only sees `q.under R` mapped into
`Localization.AtPrime q`, and `algebraMap (𝓞 ℚ) (𝓞 K) ∘ Rat.ringOfIntegersEquiv = algebraMap ℤ (𝓞 K)`,
with `IsScalarTower ℤ (𝓞 ℚ) (𝓞 K)`; the two ideals `(P.under ℤ).map _` and
`(P.under (𝓞 ℚ)).map _` in `Localization.AtPrime P` therefore coincide (`Ideal.under_under` plus the
commutation of the algebra maps).  The hypotheses `hp`, `hP`, `h0`, `hlies` are not needed for the
identity itself (the function is total); they may be used or ignored. -/
theorem ramificationIdx_under_ringOfIntegers_rat
    {K : Type*} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) (h0 : P ≠ ⊥)
    (hlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    P.ramificationIdx ℤ = P.ramificationIdx (NumberField.RingOfIntegers ℚ) := by
  haveI := hP
  -- Unfold both ramification indices: they are the lengths of the quotients by the two ideals above.
  rw [Ideal.ramificationIdx_def P ℤ,
    Ideal.ramificationIdx_def P (NumberField.RingOfIntegers ℚ)]
  rw [map_under_eq_map_under_ringOfIntegers_rat P]

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
