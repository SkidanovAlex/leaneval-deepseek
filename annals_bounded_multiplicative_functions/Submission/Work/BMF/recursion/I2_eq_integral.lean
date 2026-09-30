import Mathlib
import Submission.Work.BMF.recursion.I1I2Defs
import Submission.Work.BMF.recursion.integral_normSq_eq_card
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.I1_eq_integral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-!
# `I2` as the `L²` mean square of `F2`

This file proves the mean-value identity

`I2 S k Q p y hkS = ∫ θ, ‖F2 S k Q p y hkS θ‖²`,

i.e. the combinatorial count `I2` (pairs of tuples with pairwise distinct head modulo `p`,
every tail coordinate `≡ y (mod p)`, and equal moment vectors) is the `L²` norm squared of
the exponential sum `F2` over the same index set.

The proof is the exact analogue of the one for `F1`/`I1` (`I1_eq_integral`), composing

* `I2_eq_pairCard`: `I2` counts the pairs `(x,y)` in `i2Set` with equal moment vectors;
* `pairMomSet_card_eq` (from `I1_eq_integral`): that cardinality is the `Finset.univ` count
  on the subtype `{x // x ∈ i2Set ...}` needed by `integral_normSq_eq_card`;
* `integral_normSq_eq_card`: the `L²` mean square of a character sum equals the number of
  pairs on which the moment map agrees.
-/

namespace Work.BMF.recursion

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- `F2` is the sum of the Fourier characters indexed by the *subtype* of `i2Set`, which is
the form in which `integral_normSq_eq_card` consumes it. -/
lemma F2_eq_subtype (S k Q p y : ℕ) (hkS : k ≤ S) :
    F2 S k Q p y hkS
      = fun θ => ∑ i : {x // x ∈ i2Set S k Q p y hkS},
          UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k i.1) θ := by
  funext θ
  unfold F2
  rw [← Finset.sum_attach (i2Set S k Q p y hkS)
    (fun x => UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k x) θ)]
  rfl

theorem I2_eq_integral (S k Q p y : ℕ) (hkS : k ≤ S) :
    (I2 S k Q p y hkS : ℝ) = ∫ θ : UnitAddTorus (Fin (k + 1)), ‖F2 S k Q p y hkS θ‖ ^ 2 := by
  classical
  have hcard := pairMomSet_card_eq S k Q (i2Set S k Q p y hkS)
  have hchar := integral_normSq_eq_card (k + 1) {x // x ∈ i2Set S k Q p y hkS}
    (fun i => Submission.Vinogradov.powerSums k i.1)
  rw [I2_eq_pairCard S k Q p y hkS, hcard, ← hchar]
  apply integral_congr_ae
  filter_upwards with θ
  rw [F2_eq_subtype]

end

end Work.BMF.recursion
