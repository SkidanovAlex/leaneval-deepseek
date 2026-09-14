import Mathlib
import Submission.Vdw.FourierAssembly

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The imprimitive input in Widmer's literature shape

`FinalAssembly` splits `IrreducibleBad` into the primitive part (Cases I–III of
Bhargava's paper) and the imprimitive part `ImprimitiveBad`, whose bound
`O(H^(n-1))` is taken as an input there.  The literature result is Widmer's
theorem (`On number fields with nontrivial subfields`), quoted in the paper as

    sum over transitive imprimitive G of N_n(G,H) = O(H^(n/2+2)),

which is *stronger* than the `O(H^(n-1))` requirement as soon as `n ≥ 6`
(the exponent `n/2 + 2` is `≤ n - 1` exactly for `n ≥ 6`).  This module

* derives the `O(H^(n-1))` input from the literature-shaped bound
  (`ImprimitiveBad_isBigO_of_widmer`), and
* restates the endpoint `theorem_1_of_perIrr_literature` for `n ≥ 6` with the
  three inputs in their *literature* form: the §4 Fourier bound
  `PerIrrBound` (Case I and Case III subcase (i)), the Case-II field-counting
  bound `SubcaseI_P2`, and Widmer's bound.

For prime `n` the imprimitive input is vacuous
(`PrimeDegreePrimitive.ImprimitiveBad_isBigO_of_prime`), so `n = 3, 5, 7, …`
need only the first two inputs (`theorem_1_of_perIrr_one_prime`); the only
composite degree below `6` is `n = 4`, which needs its own (Chow–Dietmann
type) treatment of the imprimitive groups `V₄, C₄, D₈`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **Widmer's bound implies the imprimitive input for `n ≥ 6`**: from
`#ImprimitiveBad n H = O(H^(n/2+2))` one gets `O(H^(n-1))`, because
`n/2 + 2 ≤ n - 1` for `n ≥ 6` and `H ≥ 1`. -/
theorem ImprimitiveBad_isBigO_of_widmer (n : ℕ) (hn : 6 ≤ n)
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  refine hw.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH1
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hH1' : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hexp : (n : ℝ) / 2 + 2 ≤ (((n - 1 : ℕ)) : ℝ) := by
    have hn6 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hH0 _), Real.norm_of_nonneg (by positivity)]
  rw [one_mul, ← Real.rpow_natCast (H : ℝ) (n - 1)]
  exact Real.rpow_le_rpow_of_exponent_le hH1' hexp

/-- **The challenge theorem from the three literature inputs, for `n ≥ 6`**:
the §4 Fourier bound `PerIrrBound` (Case I, and Case III subcase (i) via the
window construction of `SubcaseI_P3Bound`), the Case-II field-counting bound
`SubcaseI_P2`, and Widmer's imprimitive bound `O(H^(n/2+2))`. -/
theorem theorem_1_of_perIrr_literature (n c : ℕ) (hn : 6 ≤ n) (hc : 1 ≤ c)
    (h : PerIrrBound n c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_perIrr_three n c (by omega) hc h h2 (ImprimitiveBad_isBigO_of_widmer n hn hw)

end

end Submission.Vdw
