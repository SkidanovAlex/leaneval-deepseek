/-
# ZeroFreeTables — TentRowCerts

Every row of the tent table `Work.ZeroFreeTables.tentRows` carries the sharp certificate
`TentRowCert (X, b, c)`:

`b·e^{Xc}·((Xc - 2) + (Xc + 2)·e^{-Xc}) < X·(X/2 - A₀)·c³`.

The analytic reduction of this to rational arithmetic (the exact identity
`e^{Xc}·((Xc-2)+(Xc+2)e^{-Xc}) = e^{Xc}(Xc-2) + (Xc+2)` plus the twelve-term Taylor bound
`Real.exp_bound'` for `e^{Xc/16}`, squared) is `TentRowCert_of_poly` in
`Submission.Work.ZeroFreeTables.TentRowAux`, together with the table of the rational constants
`B = n/10¹²` for each row.

Rows 2–26 are verified in the sibling modules `TentRowsB2` … `TentRowsB6`; rows 1 and 27 are
discharged here.  Finally `p ∈ tentRows` is resolved by case analysis on the twenty-seven entry
list, each case being the matching row certificate.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB88TentIf
import Submission.Work.ZeroFreeTables.TentRowAux
import Submission.Work.ZeroFreeTables.TentRowsB2
import Submission.Work.ZeroFreeTables.TentRowsB3
import Submission.Work.ZeroFreeTables.TentRowsB4
import Submission.Work.ZeroFreeTables.TentRowsB5
import Submission.Work.ZeroFreeTables.TentRowsB6

open scoped Real BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- Row 1 of `tentRows`. -/
theorem tentRow01 : TentRowCert ((6/5 : ℝ), (79700000 : ℝ)/10^9, (2840 : ℝ)/1000) := by
  refine TentRowCert_of_poly (6/5 : ℝ) ((79700000 : ℝ)/10^9) ((2840 : ℝ)/1000)
    ((1237384651244 : ℝ)/10^12) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])

/-- Row 27 of `tentRows`. -/
theorem tentRow27 : TentRowCert ((1 : ℝ), (2055 : ℝ)/10^9, (15344 : ℝ)/1000) := by
  refine TentRowCert_of_poly (1 : ℝ) ((2055 : ℝ)/10^9) ((15344 : ℝ)/1000)
    ((2609086082369 : ℝ)/10^12) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])

theorem TentRowCerts (p : ℝ × ℝ × ℝ) (hp : p ∈ Work.ZeroFreeTables.tentRows) :
    Work.ZeroFreeTables.TentRowCert p := by
  simp only [tentRows, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tentRow01
  · exact TentRowsB2.1
  · exact TentRowsB2.2.1
  · exact TentRowsB2.2.2.1
  · exact TentRowsB2.2.2.2.1
  · exact TentRowsB2.2.2.2.2
  · exact TentRowsB3.1
  · exact TentRowsB3.2.1
  · exact TentRowsB3.2.2.1
  · exact TentRowsB3.2.2.2.1
  · exact TentRowsB3.2.2.2.2
  · exact TentRowsB4.1
  · exact TentRowsB4.2.1
  · exact TentRowsB4.2.2.1
  · exact TentRowsB4.2.2.2.1
  · exact TentRowsB4.2.2.2.2
  · exact TentRowsB5.1
  · exact TentRowsB5.2.1
  · exact TentRowsB5.2.2.1
  · exact TentRowsB5.2.2.2.1
  · exact TentRowsB5.2.2.2.2
  · exact TentRowsB6.1
  · exact TentRowsB6.2.1
  · exact TentRowsB6.2.2.1
  · exact TentRowsB6.2.2.2.1
  · exact TentRowsB6.2.2.2.2
  · exact tentRow27

end Work.ZeroFreeTables
