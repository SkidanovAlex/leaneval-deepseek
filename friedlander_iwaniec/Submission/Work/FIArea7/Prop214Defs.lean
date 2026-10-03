/-
# `Work.FIArea7.Prop214Defs` — the parameters of the proof of *FI* Proposition 21.4

This module fixes the two numerical parameters used in the reduction of *FI* Proposition 21.4
(21.13) to Proposition 21.3 (21.10):

* `truncR M N` — the radius `R` of the "room" condition (20.18) of the square-wave expansion
  (20.19).  We take an integer `≥ √(MN) + 2`; then for primary `w, z` with `|w|² ≤ M`, `|z|² ≤ N`
  one has `‖w‖‖z‖ ≤ R·|Re(wz)|`, because `Re(wz)` is an odd integer, hence `|Re(wz)| ≥ 1`.

* `truncK M N` — the truncation point of the series (20.19).  The truncation adds an error
  `≪ R/(|k|-tail) ≪ R/(truncK M N)`, and there are at most `≪ (MN)²` pairs `(w,z)` (a crude
  lattice-point count in the discs suffices), so choosing `truncK M N ≍ R·M²N²` makes the total
  truncation error bounded by an absolute constant.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The radius `R` of the proof of Proposition 21.4: an integer `≥ √(MN)`, `≥ 2`. -/
def truncR (M N : ℝ) : ℕ := Nat.ceil (Real.sqrt (M * N)) + 2

/-- The truncation point of the square-wave series in the proof of Proposition 21.4. -/
def truncK (M N : ℝ) : ℕ := Nat.ceil ((truncR M N : ℝ) * M ^ 2 * N ^ 2)

end

end Work.FIArea7
