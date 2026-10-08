import Mathlib
import Submission.Work.A7REC.Char.Y6Defs

namespace Work.A7REC.Char

/-- Specialisation of `IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int` (Mathlib): for a primitive
`7`-th root of unity `ζ`, a vanishing integral combination `∑ cₖ ζᵏ` has all coefficients equal.
This is the statement that the minimal polynomial of `ζ` is `X ^ 6 + ⋯ + X + 1`. -/
theorem Y6ZetaSeven : Work.A7REC.A7ZetaSevenRelationProp := by
  intro ζ hζ c h
  exact (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int (p := 7) (by norm_num) hζ c).mp h

end Work.A7REC.Char
