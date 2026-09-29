import Mathlib
import Submission.Work.Haupt.jtp_at_pentagonal

/-!
# The even-exponent infinite product, split by residue class mod 3

For `‖u‖ < 1` the even exponents `2, 4, 6, …` of `∏' m, (1 - u ^ (2m+2))` are partitioned by
their residue class modulo `3`: exponent `6m+2` (i.e. `≡ 2`), `6m+4` (`≡ 1`) and `6m+6` (`≡ 0`).
Absolute convergence (`‖u‖ < 1`) makes the regrouping legal, giving

`∏' m, (1 - u ^ (2m+2)) = (∏' m, (1 - u ^ (6m+6))) * (∏' m, (1 - u ^ (6m+4)))
                          * (∏' m, (1 - u ^ (6m+2)))`.

This is the exact statement of `Work.Haupt.pent_triple`, whose right-hand side
`∏' k, (1 - u ^ (2(k+1)))` is the present left-hand side; only associativity and
commutativity of the (commutative) product of the three factors remain.
-/

namespace Work.Haupt

open scoped BigOperators

theorem prod_even_split (u : ℂ) (hu : ‖u‖ < 1) :
    (∏' m : ℕ, (1 - u ^ (2 * m + 2))) =
      (∏' m : ℕ, (1 - u ^ (6 * m + 6))) * (∏' m : ℕ, (1 - u ^ (6 * m + 4))) *
        (∏' m : ℕ, (1 - u ^ (6 * m + 2))) := by
  have hL : (∏' m : ℕ, (1 - u ^ (2 * m + 2)))
      = ∏' m : ℕ, (1 - u ^ (2 * (m + 1))) :=
    tprod_congr (fun m => by rw [show 2 * m + 2 = 2 * (m + 1) by ring])
  rw [hL, ← pent_triple u hu]
  ring

end Work.Haupt
