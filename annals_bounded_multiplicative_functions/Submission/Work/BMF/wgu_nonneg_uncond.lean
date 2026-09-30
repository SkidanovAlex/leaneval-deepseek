import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

/-- The weak Gowers uniformity norm is nonnegative for every function `g : ℤ → ℂ`, with no
boundedness hypothesis on `g`: it is the supremum of the terms
`(1/H) * ‖∑_{n ∈ [⌈x⌉, ⌊x+H⌋]} g n * e(-P(n))‖`, each of which is nonnegative because `H > 0`,
and the supremum of a family of nonnegative reals is nonnegative. -/
theorem wgu_nonneg_uncond (k : ℕ) (g : ℤ → ℂ) (x H : ℝ) (hH : 0 < H) :
    0 ≤ BoundedMultiplicativeFunctions.weakGowersUniformityNorm k x H g := by
  unfold BoundedMultiplicativeFunctions.weakGowersUniformityNorm
  refine Real.iSup_nonneg (fun P => ?_)
  refine Real.iSup_nonneg (fun _ => ?_)
  exact mul_nonneg (le_of_lt (one_div_pos.mpr hH)) (norm_nonneg _)

end Work.BMF
