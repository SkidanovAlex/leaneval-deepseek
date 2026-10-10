import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.minimalPrimes_height_two_of_relPrime
import Submission.Work.MotAS.ASRulV2M.coeff_X0_sq_combination
import Submission.Work.MotAS.ASRulV2M.exists_coeff_X0_sq_eq_one
import Submission.Work.MotAS.ASZplane.ZIAS_X2_saturated

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRulV2M.height_radical_ZIAS`

The AS residual chart ideal `ZIAS a b g ⊂ K[X₀,X₁,X₂]` (the chart `(1,X₀,X₁,X₂,0)` of
`V(kleinRAS)`, five cubics `zcubAS a b g k`) has

`Ideal.height (Ideal.radical (ZIAS a b g)) = 2`,

i.e. the chart of the residual curve is one-dimensional.

## What is available and what remains

Mathlib's `Ideal.height` is the *infimum* of the heights of the minimal primes
(`Mathlib/RingTheory/Ideal/Height.lean`), so the statement splits into two halves.

* **(≥ 2)** every minimal prime of `ZIAS a b g` has height at least two.  This follows from
  `Work.MotAS.minimalPrimes_height_two_of_relPrime` (proved, sorry-free) applied to two *relatively
  prime* elements of `ZIAS a b g`; the pair `zcubAS a b g 0`, `zcubAS a b g 1` is relatively prime
  (delegated as `Work.MotAS.ASRulV2M.isRelPrime_zcubAS_zero_one`; numerically the gcd of the two
  cubics is `1` for all `48` admissible `(a,b,g) ∈ (𝔽₅*)³`, the bad locus being exactly
  `a²−ab−b² = 0`).
* **(≤ 2)** some minimal prime has height at most two, i.e. the residual curve is not a finite set
  of points.  This is the geometric input of the paper's construction and is *open in this
  workspace* (see `NOTE_ZIASKB_HEIGHTLEtwo_FINDINGS.md`): the ingredient available here is
  `Work.MotAS.ASRulV2M.exists_coeff_X0_sq_eq_one` (`ZIAS a b g` contains an element monic of degree
  two in `X₀`, proved in `Submission/Work/MotAS/ASRulV2M/exists_coeff_X0_sq_eq_one.lean`), together
  with the slice certificates `zE_cert`, `zR_cert` of `Work.MotAS.ASZplane.ZIAS_X2_saturated` and
  the elimination data of `Work.MotAS.ASZPlaneModel`.  Delegated form:
  `Work.MotAS.ASRulV2M.exists_prime_height_le_two_above_ZIAS`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotAS.ASRulV2M

open MvPolynomial

/-- **The `≥ 2` half of the height computation.**

If two *relatively prime* elements of `ZIAS a b g` are available, then every minimal prime of
`ZIAS a b g` has height at least two (`Work.MotAS.minimalPrimes_height_two_of_relPrime`), and since
`Ideal.height` is the infimum of the heights of the minimal primes (and `√I` has the same minimal
primes as `I`), the height of the radical is at least two.

The coprimality hypothesis is discharged by
`Work.MotAS.ASRulV2M.isRelPrime_zcubAS_zero_one` for the pair `zcubAS a b g 0`, `zcubAS a b g 1`. -/
theorem two_le_height_radical_ZIAS_of_relPrime (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hcop : IsRelPrime (Work.MotAS.zcubAS a b g 0) (Work.MotAS.zcubAS a b g 1)) :
    (2 : ℕ∞) ≤ Ideal.height (Ideal.radical (Work.MotAS.ZIAS a b g)) := by
  rw [Ideal.height_eq_inf_minimalPrimes, Ideal.radical_minimalPrimes]
  refine le_iInf₂ fun 𝔭 h𝔭 => ?_
  exact Work.MotAS.minimalPrimes_height_two_of_relPrime _
    (Work.MotAS.zcubAS a b g 0) (Work.MotAS.zcubAS a b g 1)
    (Ideal.subset_span (Set.mem_range_self (0 : Fin 5)))
    (Ideal.subset_span (Set.mem_range_self (1 : Fin 5))) hcop 𝔭 h𝔭

/-- **The `≤ 2` half of the height computation.**

A prime `𝔭` of height at most two containing `ZIAS a b g` bounds the height of the radical: choose a
minimal prime `𝔮 ≤ 𝔭` over `ZIAS a b g`; then `𝔮.height ≤ 𝔭.height ≤ 2`, and the infimum over the
minimal primes is at most `𝔮.height`. -/
theorem height_radical_ZIAS_le_two_of_exists_prime (K : Type) [Field K] [CharP K 5] (a b g : K)
    (h : ∃ 𝔭 : Ideal (MvPolynomial (Fin 3) K),
      𝔭.IsPrime ∧ Work.MotAS.ZIAS a b g ≤ 𝔭 ∧ 𝔭.height ≤ 2) :
    Ideal.height (Ideal.radical (Work.MotAS.ZIAS a b g)) ≤ 2 := by
  obtain ⟨𝔭, h𝔭prime, hle, hht⟩ := h
  haveI := h𝔭prime
  obtain ⟨𝔮, h𝔮mem, h𝔮le⟩ := Ideal.exists_minimalPrimes_le (I := Work.MotAS.ZIAS a b g) hle
  rw [Ideal.height_eq_inf_minimalPrimes, Ideal.radical_minimalPrimes]
  refine le_trans (le_trans (iInf_le _ 𝔮) (iInf_le _ h𝔮mem)) ?_
  exact le_trans (Ideal.height_mono h𝔮le) hht

theorem height_radical_ZIAS (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hg : g ≠ 0) (hA : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    Ideal.height (Ideal.radical (Work.MotAS.ZIAS a b g)) = 2 := by sorry

end Work.MotAS.ASRulV2M
