import Mathlib
import Submission.Work.QuadraticFields.MultiquadraticInside

/-!
# `p ∤ discr K` forces trivial ramification at `p`

If a rational prime `p` does not divide the discriminant of a number field `K`, then `p` is
unramified in `K`, so every prime `P` of `𝓞 K` above `p` has ramification index one.

This is the "easy" half of the classical equivalence: `p` ramifies in `K` if and only if
`p ∣ discr K`. The nontrivial input is Mathlib's
`NumberField.not_dvd_discr_iff_forall_mem`, which converts `¬ p ∣ discr K` into
`Algebra.IsUnramifiedAt ℤ P`; the remaining step transfers unramifiedness along the scalar tower
`ℤ → 𝓞 ℚ → 𝓞 K`, over which the ramification index of `P` is computed, and applies
`Ideal.ramificationIdx_eq_one`.
-/

namespace Work.QuadraticFields

theorem ramificationIdx_eq_one_of_not_dvd_discr {K : Type*} [Field K] [NumberField K]
    (p : ℕ) (hp : Nat.Prime p) (h : ¬ (p : ℤ) ∣ NumberField.discr K)
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime]
    (hP : (p : NumberField.RingOfIntegers K) ∈ P) :
    P.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1 := by
  -- `p`, viewed in `ℤ`, is prime.
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- The hypothesis `p ∈ P` is the one required by the Mathlib criterion, stated over `ℤ`.
  have hmem : ((p : ℤ) : NumberField.RingOfIntegers K) ∈ P := by
    simpa using hP
  -- `¬ p ∣ discr K` means `P` is unramified over `ℤ`.
  have hunr : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem K (NumberField.RingOfIntegers K) hpi).mp h P
      inferInstance hmem
  -- Unramifiedness restricts along the tower `ℤ → 𝓞 ℚ → 𝓞 K`, which is the base ring of the
  -- ramification index appearing in the statement.
  have hunr' : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers ℚ) P :=
    Algebra.IsUnramifiedAt.of_restrictScalars ℤ P
  exact Ideal.ramificationIdx_eq_one P (NumberField.RingOfIntegers ℚ)

end Work.QuadraticFields
