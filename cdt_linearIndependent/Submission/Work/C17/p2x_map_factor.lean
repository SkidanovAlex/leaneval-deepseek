import Mathlib
import Submission.Work.C17.p2x_defs
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.led_factor
import Submission.Work.C17.led_real_data

namespace Work.C17

/-- `P2x = (X−1)·X·(X+1)·Q4x` becomes, over `ℂ`, the septic `GAB c d` of `p2x_defs`,
where `c = ledC a b`, `d = ledD a b` are the two traces of the quadratic factors of `Q4x`
(`led_factor`).  This is the bridge between the `ℚ`-model of the operator `M` and its
`ℂ`-model used by the local/holonomy analysis. -/
theorem p2x_map_factor (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    (Work.C17.P2x a b).map (algebraMap ℚ ℂ)
      = Work.C17.GAB (((Work.C17.ledC a b : ℝ)) : ℂ) (((Work.C17.ledD a b : ℝ)) : ℂ) := by
  rw [P2x, GAB]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_one,
    Polynomial.map_X]
  rw [led_factor a b ha hb]

end Work.C17
