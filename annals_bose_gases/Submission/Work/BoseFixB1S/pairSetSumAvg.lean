import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseFixB1S.boxPairQCount_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.pairSetSumAvg`

Symmetrisation of a sum over the ordered distinct-pair set `pairSet N`:

    ∑_{p ∈ pairSet N} (g p.1 + g p.2)/2 = (N − 1) · ∑ i, g i .

Since `pairSet N` consists of the *ordered* pairs `(i,j)` with `i ≠ j`, the
first-coordinate sum and the second-coordinate sum are both `(N−1)·Σg`
(`BoseGases.sum_pairSet_first_eq`, `BoseGases.sum_pairSet_second_eq`); averaging
them gives the claim.
-/

namespace Work.BoseFixB1S

theorem pairSetSumAvg {N : ℕ} (g : Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, (g p.1 + g p.2) / 2)
      = ((N : ℝ) - 1) * ∑ i : Fin N, g i := by
  have h1 := Submission.BoseGases.sum_pairSet_first_eq N g
  have h2 := Submission.BoseGases.sum_pairSet_second_eq N g
  have h : (∑ p ∈ Submission.BoseGases.pairSet N, (g p.1 + g p.2) / 2)
      = ((∑ p ∈ Submission.BoseGases.pairSet N, g p.1)
        + (∑ p ∈ Submission.BoseGases.pairSet N, g p.2)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [h, h1, h2]
  ring

end Work.BoseFixB1S
