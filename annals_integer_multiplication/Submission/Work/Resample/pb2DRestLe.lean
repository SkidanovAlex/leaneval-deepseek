import Mathlib
import Submission.Work.Resample.pb2CostDefs
import Submission.Work.Resample.pbCostArithKit
import Submission.Work.Resample.paDRestLit
import Submission.Work.Resample.pbBracketLeTight
import Submission.Work.Resample.pb2DLayout

namespace Work.Resample

open HvdH

set_option autoImplicit false

/-- **Layout and absorption for the `B̃` half.**  The layout, `isz` and constant terms
`pb2DRest` of the per-axis budget `PB2Br` (mirror of `Work.Resample.paDRest`, with the prefix
product taken from `ss` and the suffix product from `ts`) are absorbed by the `ts.prod * p^2` term
of `HvdH.resCost`, with the same explicit constant `2^24 * D^3 * (D+5)`. -/
theorem pb2DRestLe {p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts)
    (Kb j : ℕ) (hj : j < HvdH.D) :
    Work.Resample.pb2DRest Kb p ss ts j
      ≤ (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) * (ts.prod * p ^ 2) := by
  -- the mirrored layout facts (`Work.Resample.pb2DLayout`)
  obtain ⟨hT, hX, hXsz, hA, hB, hs, ht⟩ := pb2DLayout h j hj
  obtain ⟨-, -, hp100, -, -, -⟩ := h
  have hp : 1 ≤ p := by omega
  -- the four `isz` bounds, all of the shape `size + 2`
  have hAisz : HvdH.isz (((ss.take j).prod : ℕ) : ℤ) ≤ ts.prod + 2 := by
    rw [paDL_isz_natCast]
    have hsz : (ss.take j).prod.size ≤ ts.prod :=
      le_trans (Nat.size_le_size hA) (pbca_size_le ts.prod)
    omega
  have hBisz : HvdH.isz (((ts.drop (j + 1)).prod : ℕ) : ℤ) ≤ ts.prod + 2 := by
    rw [paDL_isz_natCast]
    have hsz : (ts.drop (j + 1)).prod.size ≤ ts.prod :=
      le_trans (Nat.size_le_size hB) (pbca_size_le ts.prod)
    omega
  have hsisz : HvdH.isz (((ss.getD j 0 : ℕ)) : ℤ) ≤ p + 2 := by
    rw [paDL_isz_natCast]; omega
  have htisz : HvdH.isz (((ts.getD j 0 : ℕ)) : ℤ) ≤ p + 2 := by
    rw [paDL_isz_natCast]; omega
  -- the seven summands of `pb2DRest` are exactly the abstract shape of `paDL_arith`
  unfold pb2DRest
  exact paDL_arith
    ((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1))
    (HvdH.isz (((ss.take j).prod : ℕ) : ℤ))
    (HvdH.isz (((ts.drop (j + 1)).prod : ℕ) : ℤ))
    (HvdH.isz (((ss.getD j 0 : ℕ)) : ℤ))
    (HvdH.isz (((ts.getD j 0 : ℕ)) : ℤ))
    ts.prod p hT hp hX hXsz hAisz hBisz hsisz htisz

end Work.Resample
