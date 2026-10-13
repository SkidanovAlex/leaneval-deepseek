/-
# `Work.H2.T1Q.QDefs` — the vocabulary of the interior `T1Easy` estimate

The target `Work.H2.T1Q.EasyBoundQ` bounds the "easy part"
`T1Easy α f g = H4PairInt α (f · D_θg) g - T1Hard α f g` of Elgindi's `Transport1`
pairing in the *interior* class (`Work.FTS.LocData.SmoothQuad`, genuine `C^∞` on the open
quadrant) with the pointwise hypotheses of the paper on the open quadrant.

This file fixes the two objects that the expansion lemma and the estimate speak about:

* `EasySumQ α f g` — the finite Leibniz sum of `H4PairInt α (f · D_θg) g` with the five
  summands of `T1Hard` removed; the expansion `T1Easy_expandQ` proves
  `T1Easy α f g z θ = EasySumQ α f g z θ` on the open quadrant;
* `abs_EasySumQ_le_EasyMajor` — the (hypothesis-free) majorisation by the pointwise
  absolute-value majorant `Work.FTS.H2.EasyMajor` of the closed-quadrant template
  `Submission/Work/FTS/H2/T1EasyBound.lean`.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.H2.T1EasyBound

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 800000

open Work.FTS.H2

/-- The finite Leibniz sum of the "easy part" of the pairing
`H4PairInt α (f · D_θg) g - T1Hard α f g`: all the Leibniz summands `xD` and `yM` of the
expansion of `H4PairInt α (f · D_θg) g` except the five summands of `T1Hard` (the `D_z`-slot
summand `(i,b) = (4,0)` and the four mixed-slot summands `(a,b) = (0,0)` with `i + j = 4`). -/
def EasySumQ (α : ℝ) (f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
        (if i = 4 ∧ b = 0 then 0 else xD f g i b z θ))
      + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else yM α f g i j a b z θ)
           else 0)

/-- The pointwise absolute-value majorant `EasyMajor` dominates `|EasySumQ|` — the same
finite sum with every summand replaced by its absolute value.  No hypothesis is needed. -/
theorem abs_EasySumQ_le_EasyMajor (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    |EasySumQ α f g z θ| ≤ EasyMajor α f g z θ := by
  rw [EasySumQ, EasyMajor]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases h : i = 4 ∧ b = 0
    · simp [h]
    · simp [h]
  · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · simp only [if_pos hc]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun a _ => ?_
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun b _ => ?_
      by_cases h : a = 0 ∧ b = 0 ∧ i + j = 4
      · simp [h]
      · simp [h]
    · simp [hc]

end Work.H2.T1Q
