import Mathlib

namespace Work.CRed

/-- Independence of `![1, x, y, x*y]` is preserved when `x` and `y` are negated: the
family `![1, -x, -y, x*y]` is obtained from `![1, x, y, x*y]` by multiplying the `i`-th
entry by the unit `(1, -1, -1, 1)_i` of `ℚ`, and a family is linearly independent over a
ring iff its `Rˣ`-multiples are. -/
lemma li_neg_family (x y : ℝ) :
    LinearIndependent ℚ ![1, x, y, x * y] → LinearIndependent ℚ ![1, -x, -y, x * y] := by
  intro h
  have hw : LinearIndependent ℚ ((![1, -1, -1, 1] : Fin 4 → ℚˣ) • ![1, x, y, x * y]) :=
    h.units_smul _
  convert hw using 1
  ext i
  fin_cases i <;> simp

end Work.CRed
