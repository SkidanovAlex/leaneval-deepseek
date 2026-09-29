import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buWdKit

/-!
# Intermediate values of the shift word of `Work.Resample.buWdDiv`

The word of `Work.Resample.buWdDiv` forms the shift exponent
`k = auPrec p - p + (2α² - 2)` from the entries `p` and `α` of the canonical block `buCB`,
pushing the following integers (~ `Int`) on top of the window, in this order:

`buDivZ1 α` (`α·α`, `IntLib.mulS`), `buDivZ2 α` (`dup`+`add`), `buDivZ3 α` (push `2`, `sub`),
`buDivZ4 p` (push `50`, `add`), `buDivZ5 p` (`dup`+`add`), and finally `buDivK p α = buDivZ5 p + buDivZ3 α`.

The arithmetic facts used downstream are `(buDivK p α).toNat = auPrec p - p + (2α² - 2)` and
`isz v ≤ buSZ p` for every intermediate value (`buDivArith`, `buDivSizes`).
-/

set_option autoImplicit false

namespace Work.Resample

/-- `α · α` as an integer (`IntLib.mulS` on two copies of `α`). -/
def buDivZ1 (α : ℕ) : ℤ := (α : ℤ) * (α : ℤ)

/-- `2 · α²` (`dup` followed by `add`). -/
def buDivZ2 (α : ℕ) : ℤ := buDivZ1 α + buDivZ1 α

/-- `2 · α² - 2` (push `2`, `sub`). -/
def buDivZ3 (α : ℕ) : ℤ := buDivZ2 α - 2

/-- `50 + p` (push `50`, `add`). -/
def buDivZ4 (p : ℕ) : ℤ := 50 + (p : ℤ)

/-- `2 · (p + 50)` (`dup` followed by `add`). -/
def buDivZ5 (p : ℕ) : ℤ := buDivZ4 p + buDivZ4 p

/-- The shift exponent formed by the word: `2p + 98 + 2α² = auPrec p - p + (2α² - 2)`. -/
def buDivK (p α : ℕ) : ℤ := buDivZ5 p + buDivZ3 α

end Work.Resample
