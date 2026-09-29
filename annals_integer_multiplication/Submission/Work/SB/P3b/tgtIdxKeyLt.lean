import Mathlib
import Submission.Work.SB.P3b.Base
import Submission.Work.SB.P3.tgtInvFacts

namespace Work.SB.P3b

/-- The index map of the output layout, restricted to the flat range `range (A*B*n)`, stays inside
that range.  All the positivity hypotheses need (`0 < n`, `0 < B`) follow from `i < A*B*n`, since
a product is positive iff both factors are; the bounded range estimate itself is
`Work.SB.P3.tgtInvFacts`. -/
theorem tgtIdxKeyLt (A n B i : ℕ) (hi : i < A * B * n) :
    Work.Layout.tgtIdx n B (i / n) (i % n) < A * B * n := by
  have hpos : 0 < A * B * n := lt_of_le_of_lt (Nat.zero_le i) hi
  have hAB : 0 < A * B := Nat.pos_of_mul_pos_right hpos
  have hn : 0 < n := Nat.pos_of_mul_pos_left hpos
  have hB : 0 < B := Nat.pos_of_mul_pos_left hAB
  exact (Work.SB.P3.tgtInvFacts A n B hn hB).1 i hi

end Work.SB.P3b
