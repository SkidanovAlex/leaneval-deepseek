import Mathlib
import Submission.Vdw.FinalAssembly
import Submission.Vdw.FourierIndexBound
import Submission.Vdw.PrimeDegreePrimitive
import Submission.Vdw.SubcaseI_P3Bound

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The challenge theorem from the §4 index-form Fourier bound

Combining `FourierIndexBound.perDDiscBound_of_perIrrBound` (the paper's
Corollary `fbound2`, in index-condition form, implies the per-discriminant
fiber bound `PerDDiscBound`) with the final assembly
`FinalAssembly.theorem_1_of_perD`:

* `theorem_1_of_perIrr` — the challenge statement follows from
  `PerIrrBound n c` (the §4 Fourier input in its canonical `fbound2` shape)
  plus the three region bounds `SubcaseI_P2`, `SubcaseI_P3`, `ImprimitiveBad`;
* `theorem_1_of_perIrr_prime` — for prime `n` the imprimitive input is
  vacuous (`PrimeDegreePrimitive`), leaving two region bounds;
* `theorem_1_of_perIrr_three` — the subcase-(i) region `SubcaseI_P3` is
  DISCHARGED from `PerIrrBound` (`SubcaseI_P3_isBigO_of_perIrrBound`, the
  window construction of `SubcaseI_P3Bound`), leaving the §4 Fourier input
  plus only the Case-II region bound and the imprimitive bound;
* `theorem_1_of_perIrr_one_prime` — in prime degree, only the §4 Fourier
  input and the Case-II bound remain.

The current, sharpest form of the reduction is in `FourierDequi`, where the
input is the paper's Corollary `Dequi2` (multi-prime, `DequiBound`) and
`perDDiscBound_of_perIrrBound` is derived from the index-form input
`PerIrrBound`.  Note that `PerIrrBound` carries the hypothesis `2 ≤ D`:
without it the `D = 1` case is false (the condition set is the whole box) and
the reduction would be vacuous — see the Roadmap Session-139 block.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

/-- **The challenge theorem from the index-form Fourier bound.** -/
theorem theorem_1_of_perIrr (n c : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c) (h : PerIrrBound n c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_perD n (max (c * smallConst n + 1) (smallConst n * (2 * smallConst n + 1) ^ n))
    hn (by omega) (perDDiscBound_of_perIrrBound n c hn hc h) h2 h3 h4

/-- **The challenge theorem in prime degree**: the imprimitive input is
vacuous, leaving the §4 Fourier bound and the two region bounds. -/
theorem theorem_1_of_perIrr_prime (n c : ℕ) (hn : 3 ≤ n) (hprime : Nat.Prime n) (hc : 1 ≤ c)
    (h : PerIrrBound n c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_perIrr n c hn hc h h2 h3 (ImprimitiveBad_isBigO_of_prime n hprime)

 /-- **The challenge theorem from the §4 Fourier bound with the subcase-(i)
region discharged**: `SubcaseI_P3` is bounded from `PerIrrBound` alone
(`SubcaseI_P3_isBigO_of_perIrrBound`), so only the Case-II region and the
imprimitive region remain as hypotheses. -/
theorem theorem_1_of_perIrr_three (n c : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c) (h : PerIrrBound n c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_perIrr n c hn hc h h2 (SubcaseI_P3_isBigO_of_perIrrBound n c hn hc h) h4

/-- **The challenge theorem in prime degree with the subcase-(i) region
discharged**: only the §4 Fourier input and the Case-II region bound remain
(the imprimitive bound is vacuous in prime degree). -/
theorem theorem_1_of_perIrr_one_prime (n c : ℕ) (hn : 3 ≤ n) (hprime : Nat.Prime n)
    (hc : 1 ≤ c) (h : PerIrrBound n c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_perIrr_prime n c hn hprime hc h h2
    (SubcaseI_P3_isBigO_of_perIrrBound n c hn hc h)

end Submission.Vdw
