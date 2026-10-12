import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.LocRepoint.chiMass_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocRepoint

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory
open Submission.BoseGases

set_option autoImplicit false

/-- **The pointwise `u`-normalisation of the repointed cutoff.**

For every `x`, the `u`-integral of `χ_{B(u)}(x)²` collapses to `χ(x/L)²`: the two factors
separate (`chiSmallB M L d u x = chiScale L x · χ_M((L·d)⁻¹•x − u)`), the constant
`χ(x/L)²` comes out, and the remaining `u`-integral of `χ_M((L·d)⁻¹•x − u)²` is `∫χ_M² = 1`
by translation invariance.  No integrability hypothesis is needed: both
`integral_const_mul` and `integral_sub_left_eq_self` are unconditional. -/
theorem chiSmallB_sq_integral_u {M : ℕ} (hM : 1 ≤ M) {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), (Work.LocRepoint.chiSmallB M L d u x) ^ 2)
      = (Submission.BoseGases.chiScale L x) ^ 2 := by
  have hmul : (fun u : ℝ³ => (chiSmallB M L d u x) ^ 2)
      = fun u : ℝ³ => (chiScale L x) ^ 2 * (chiSmall M ((L * d)⁻¹ • x - u)) ^ 2 := by
    funext u
    simp only [chiSmallB, mul_pow]
  rw [hmul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_left_eq_self (fun v : ℝ³ => (chiSmall M v) ^ 2) volume
      ((L * d)⁻¹ • x), chiSmall_L2 hM, mul_one]

end Work.LocRepoint
