import Submission.Vdw.FinalAssembly
import Submission.Vdw.PrimeDegreePrimitive

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The challenge theorem in prime degree: three residual inputs suffice

Combining the final assembly (`FinalAssembly.theorem_1_of_perD`) with the
vanishing of `ImprimitiveBad` in prime degree
(`PrimeDegreePrimitive.ImprimitiveBad_isBigO_of_prime`) removes the
imprimitive (Widmer) input from the reduction whenever `n` is prime:

    theorem_1_of_perD_prime :
      PerDDiscBound n c → #SubcaseI_P2 = O(H^(n-1)) → #SubcaseI_P3 = O(H^(n-1))
        → E n H = O(H^(n-1))          (n ≥ 3 prime).

In particular for `n = 3` and `n = 5` (the two prime degrees `≥ 3` for which
the paper's Case analysis is not superseded by small-`n` results) the
challenge statement follows from three literature inputs instead of four.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

/-- **The challenge theorem for prime `n`, given the three remaining residual
inputs**: the per-discriminant Fourier bound `PerDDiscBound`, the Case-II
bound `SubcaseI_P2` (`D_f ≤ H^(2+2δ)`) and the Case-III-subcase-(i) bound
`SubcaseI_P3` (`C_f > H^(1+δ)`).  The imprimitive input is vacuous because a
transitive group of prime degree is primitive. -/
theorem theorem_1_of_perD_prime (n c : ℕ) (hn : 3 ≤ n) (hprime : Nat.Prime n) (hc : 1 ≤ c)
    (hper : PerDDiscBound n c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_perD n c hn hc hper h2 h3 (ImprimitiveBad_isBigO_of_prime n hprime)

/-- Degree `3`. -/
theorem theorem_1_of_perD_three (c : ℕ) (hc : 1 ≤ c) (hper : PerDDiscBound 3 c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 3 H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 3 H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ))) :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_perD_prime 3 c (by norm_num) (by norm_num) hc hper h2 h3

/-- Degree `5`. -/
theorem theorem_1_of_perD_five (c : ℕ) (hc : 1 ≤ c) (hper : PerDDiscBound 5 c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 5 H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (5 - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 5 H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (5 - 1) : ℝ))) :
    (fun H : ℕ => (E 5 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (5 - 1) : ℝ)) :=
  theorem_1_of_perD_prime 5 c (by norm_num) (by norm_num) hc hper h2 h3

end Submission.Vdw
