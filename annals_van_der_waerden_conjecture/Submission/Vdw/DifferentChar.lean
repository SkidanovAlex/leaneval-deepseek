import Mathlib
import Submission.Vdw.DifferentValuation

open scoped Classical NumberField

set_option autoImplicit false

/-!
# Characterising the different-ideal exponent by the ramification index

For a number field `K` with ring of integers `𝒪`, the **different ideal**
`differentIdeal ℤ 𝒪` (whose `absNorm` is `|discr K|`) records at each prime
`P` the different exponent `m_P := v_P(𝔡)`.  Mathlib's modern ramification
API gives the clean characterisations:

* `P ∣ 𝔡  ↔  P.ramificationIdx ℤ ≠ 1`  (ramified primes are exactly the
  primes dividing the different; the unramified case `e_P = 1` is
  `Algebra.IsUnramifiedAt`, equivalent to `P.ramificationIdx ℤ = 1` over the
  perfect residue fields `F_p` of `ℤ`), and
* the unramified half of the tame-different programme: `m_P = 0` when
  `e_P = 1` (`DifferentValuation` already had the free lower bound
  `P^(e_P−1) ∣ 𝔡`, i.e. `m_P ≥ e_P − 1`, from
  `Ideal.pow_sub_one_dvd_differentIdeal`).

These two facts are the `e_P = 1` base case of the tame theorem
`m_P = e_P − 1` (for `p ∤ e_P`, p tame), whose general case is the subject of
the local-field programme recorded in `Roadmap.lean`.
-/

namespace Submission.Vdw

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- A prime ideal divides the different ideal iff its ramification index is
not `1` (equivalently: it is ramified). -/
theorem prime_dvd_differentIdeal_iff_ramIdx_ne_one (P : Ideal (𝓞 K)) [P.IsPrime] :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P.ramificationIdx ℤ ≠ 1 := by
  rw [dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 K) (P := P)]
  rw [← Ideal.ramificationIdx_eq_one_iff (q := P) (R := ℤ)]

/-- A prime ideal does not divide the different ideal iff its ramification
index is `1` (unramified primes have different-ideal exponent `0`). -/
theorem differentIdeal_not_dvd_iff_ramIdx_one (P : Ideal (𝓞 K)) [P.IsPrime] :
    ¬ P ∣ differentIdeal ℤ (𝓞 K) ↔ P.ramificationIdx ℤ = 1 := by
  rw [not_dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 K) (P := P)]
  rw [Ideal.ramificationIdx_eq_one_iff (q := P) (R := ℤ)]

/-- A ramified prime (`2 ≤ e_P`) divides the different ideal with positive
exponent: `m_P ≥ 1`.  (Free direction from
`P^(e_P−1) ∣ differentIdeal`, the `DifferentValuation`-style lower bound.) -/
theorem prime_dvd_differentIdeal_of_ramIdx_two (P : Ideal (𝓞 K)) [P.IsPrime]
    (hP : 2 ≤ P.ramificationIdx ℤ) :
    P ∣ differentIdeal ℤ (𝓞 K) := by
  -- e ≥ 2, so e ≠ 1 and the characterisation applies
  exact (prime_dvd_differentIdeal_iff_ramIdx_ne_one (K := K) (P := P)).2 (by omega)

/-- An unramified prime (`e_P = 1`) does not divide the different ideal
(exponent `m_P = 0`). -/
theorem differentIdeal_not_dvd_of_ramIdx_one (P : Ideal (𝓞 K)) [P.IsPrime]
    (hP : P.ramificationIdx ℤ = 1) :
    ¬ P ∣ differentIdeal ℤ (𝓞 K) := by
  exact (differentIdeal_not_dvd_iff_ramIdx_one (K := K) (P := P)).2 hP

end
end Submission.Vdw
