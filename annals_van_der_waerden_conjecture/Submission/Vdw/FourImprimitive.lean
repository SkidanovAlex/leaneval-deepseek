import Submission.Vdw.QuarticSymmBound
import Submission.Vdw.FinalEndpoints

open Polynomial Filter Asymptotics
open scoped BigOperators
open vanDerWaerdenConjecture

set_option autoImplicit false

/-!
# Degree `4`: the imprimitive input is a **theorem**

`FinalEndpoints.theorem_1_of_literature_four` reduced the challenge statement in degree `4`
to three inputs: the Lemke Oliver–Thorne per-field fibre bound, the exact quartic field
count, and an `O(H^3)` bound for the *imprimitive* quartics (`H^(n/2+2) = H^4` from
Widmer is not enough).

`QuarticSymmBound` proves that imprimitive bound (`ImprimitiveBad_four_isBigO`), so in
degree `4` only the two classical field-counting inputs remain.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

/-- **Degree 4**: the challenge theorem from the per-field fibre bound and the exact quartic
field count — the imprimitive input is supplied by `ImprimitiveBad_four_isBigO`. -/
theorem theorem_1_of_literature_four_imprimitive_proved
    (hLOT : PerFieldFibreBound 4 (by omega : 1 ≤ 4))
    (hSC : FieldCountBound 4 (by omega : 1 ≤ 4) 1) :
    (fun H : ℕ => (E 4 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ)) := by
  refine theorem_1_of_literature_four hLOT hSC ?_
  have h : (fun H : ℕ => ((ImprimitiveBad 4 H).ncard : ℝ))
      =O[atTop] (fun H : ℕ => (H : ℝ) ^ (4 - 1)) := by
    simpa using ImprimitiveBad_four_isBigO
  exact h

/-- **The imprimitive input for every degree `n ≥ 3`** (given Widmer's bound, which is
available for all `n`): vacuous in prime degree (`n = 3, 5`), the Chow–Dietmann count for
`n = 4` (`ImprimitiveBad_four_isBigO`), and Widmer's `O(H^(n/2+2))` for `n ≥ 6`. -/
theorem ImprimitiveBad_isBigO_complete (n : ℕ) (hn : 3 ≤ n)
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  rcases eq_or_lt_of_le hn with h3 | h4
  · subst h3
    exact ImprimitiveBad_isBigO_of_prime 3 (by norm_num)
  · rcases eq_or_lt_of_le (show 4 ≤ n by omega) with h4' | h5
    · subst h4'
      simpa using ImprimitiveBad_four_isBigO
    · rcases eq_or_lt_of_le (show 5 ≤ n by omega) with h5' | h6
      · subst h5'
        exact ImprimitiveBad_isBigO_of_prime 5 (by norm_num)
      · exact ImprimitiveBad_isBigO_of_widmer n (by omega) hw

end Submission.Vdw
