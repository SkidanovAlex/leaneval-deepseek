import Mathlib
import Submission.Work.TMContract.Defs

/-!
# The `1`-periodic core of the Prüfer lift `pruferStep`

`Work.TMContract.pruferStep a t` is the Prüfer angle (in half-turns) of the vector
`(cos πt, sin πt)` under the companion matrix `!![a,-1;1,0]`.  It is built from the floor
`k = ⌊t + 1/2⌋`: writing `t = k + r - 1/2` with `r = Int.fract (t + 1/2) ∈ [0,1)`, the
value is `k + pruferCore a r`.  The function `pruferCore a : ℝ → ℝ` is the periodic part;
it is continuous on `[0,1]` with equal values `1/2` at `0` and `1`, which is exactly the
"gluing" hypothesis of `ContinuousOn.comp_fract` allowing the continuity of `pruferStep`
to be proved from continuity of the periodic core.
-/

namespace Work.TMC13

noncomputable section

/-- The `1`-periodic core of `pruferStep`: for `r = Int.fract (t + 1/2)` one has
`pruferStep a t = t + pruferCore a r`.  The value at `r = 1` is chosen (`π/2`, i.e. the
value `1/2` of the core) to make the core continuous on `[0,1]`. -/
def pruferCore (a r : ℝ) : ℝ :=
  1 - r + (if r = 1 then Real.pi / 2 else if r = 0 then -(Real.pi / 2)
    else Real.arctan (Real.tan (Real.pi * (r - 1 / 2)) - a)) / Real.pi

theorem pruferCore_zero (a : ℝ) : pruferCore a 0 = 1 / 2 := by
  rw [pruferCore, if_neg (by norm_num : (0:ℝ) ≠ 1), if_pos rfl]
  field_simp
  ring

theorem pruferCore_one (a : ℝ) : pruferCore a 1 = 1 / 2 := by
  rw [pruferCore, if_pos rfl]
  field_simp
  ring

end

end Work.TMC13
