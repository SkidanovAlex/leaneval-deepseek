import Mathlib
import Submission.Work.BMF.V4prelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Vinogradov–Korobov denominator at exponent `6/7`

`VKD67 N t = (log(|t|+3))^{6/7} · (log(N+2) + log log(|t|+3))` is the denominator occurring in the
Vinogradov–Korobov zero-free region of exponent `6/7` (`V3`) and in the logarithmic-derivative
bound `V4`.

Writing it through the abbreviations `Work.BMF.VKA` and `Work.BMF.VKE` of `V4prelim` lets the
elementary lemmas of that file (monotonicity under a shift of the height by at most `1`,
`VKA_shift_le`, `VKE_shift_le`) be reused verbatim.
-/

namespace Work.BMF.VKPrimeSums

/-- The Vinogradov–Korobov denominator at exponent `6/7`:
`VKD67 N t = (log(|t|+3))^{6/7} · (log(N+2) + log log(|t|+3))`. -/
noncomputable def VKD67 (N : ℕ) (t : ℝ) : ℝ :=
  Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t

lemma VKD67_eq' (N : ℕ) (t : ℝ) :
    VKD67 N t = Work.BMF.VKA t ^ (6 / 7 : ℝ) * Work.BMF.VKE N t := rfl

/-- Unfolding the definition into the explicit expression appearing in the statements. -/
lemma VKD67_eq (N : ℕ) (t : ℝ) :
    VKD67 N t = Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
      (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := rfl

end Work.BMF.VKPrimeSums
