import Mathlib
import Submission.Work.SG.SGprelude
import Submission.Work.SG.imatOfList_inj

/-!
# Associativity of the flat `3 × 3` matrix product `m9mul`

`m9mul a b` (`Defs.m9mul`) is the row-major flat product of two "matrices" presented as lists of
integers; entries are read with `getD _ 0`, so missing entries count as `0` and entries past the
ninth are invisible.  Reading a flat list as a matrix with the very same padding convention,
`imatOfList l = Matrix.of fun i j => l.getD (3 * i + j) 0`, turns the flat product into genuine
matrix multiplication: `imatOfList_mul` (`SGprelude`) proves
`imatOfList (m9mul a b) = imatOfList a * imatOfList b` for *arbitrary* lists `a b`.

Consequently associativity of `m9mul` is inherited from `Matrix.mul_assoc`.  The only extra input
is that the two sides denote the same flat list: both have length `9` (`length_m9mul`) and
`imatOfList` is injective on lists of length `9` (`imatOfList_inj`).
-/

namespace Work.SG

/-- The flat matrix product is associative.  No hypothesis is needed: `m9mul` only ever reads the
first nine entries of its arguments (`getD _ 0`), so the padded lists and the matrices they denote
determine each other. -/
theorem zassoc_m9mul_assoc (a b c : List ℤ) : m9mul (m9mul a b) c = m9mul a (m9mul b c) := by
  refine imatOfList_inj (length_m9mul (m9mul a b) c) (length_m9mul a (m9mul b c)) ?_
  simp only [imatOfList_mul, Matrix.mul_assoc]

end Work.SG
