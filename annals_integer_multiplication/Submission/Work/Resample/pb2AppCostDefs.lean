import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pb2Defs

/-!
# Shared definition for the cost arithmetic of one axis step of the `B̃` pass

`pb2AppCost` is the mirror of `Work.Resample.paAppCost` (`Submission/Work/Resample/paApplyDCost.lean`)
for the `B` half of paper Theorem 4.1: the total cost bound of the phases of one axis step of
`Work.Resample.pb2ApplyE`, in the order in which they are run (`LayoutLib.applyAlong`, park,
`WordP.clearRgn`, unpark, move stack 7, move stack 6, `mulNatWord`, store on stack 6).  The
constants `Kal, Kp, Ku, Km7, Km6, Km2, Kmul` are those of the seven library words involved.

As opposed to the `Ã` half, the array of axis `j` has shape
`(ss.take j).prod × ts.getD j 0 × (ts.drop (j+1)).prod` (the input shape is `ts`), the running
outer product lives on stack 6 as `(ss.take j).prod`, stack 7 holds the *input* dimension
`ts.getD j 0` and the slice word's cost carries the extra `Kb (t+1) (p+1)²` term of
`Work.Resample.SliceSpecAt`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- Total cost bound of the phases of `pb2ApplyE`, in the order in which they are run. -/
def pb2AppCost (Kal Kmul Kb Kp Ku Km7 Km6 Km2 : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ)
    (j : ℕ) (Pj : List Val) (nw : Val) : ℕ :=
  (ss.take j).prod * (ts.drop (j + 1)).prod *
      (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) +
        Kb * (ts.getD j 0 + 1) * (p + 1) ^ 2)
  + Kal * ((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1)
  + Kal * (isz ((ss.take j).prod : ℤ) + isz ((ss.getD j 0 : ℕ) : ℤ) +
      isz ((ts.getD j 0 : ℕ) : ℤ) + isz (((ts.drop (j + 1)).prod : ℕ) : ℤ))
  + (Kp * (vsz nw + 1)
      + ((5 * ((Pj.map vsz).sum + 1) + 2)
        + (Ku * (vsz nw + 1)
          + (Km7 * (vsz (Val.int ((ss.getD j 0 : ℕ) : ℤ)) + 1)
            + (Km6 * (vsz (Val.int (((ss.take j).prod : ℕ) : ℤ)) + 1)
              + (Kmul * (((ss.take j).prod).size + 1) * ((ss.getD j 0).size + 1)
                + Km2 * (vsz (Val.int ((((ss.take j).prod) * (ss.getD j 0) : ℕ) : ℤ)) + 1)))))))

end Work.Resample
