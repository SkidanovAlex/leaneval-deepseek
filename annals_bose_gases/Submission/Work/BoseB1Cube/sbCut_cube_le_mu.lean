import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.BoseFixB1S.sbCut_cube_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.sbCut_cube_le_mu`

FS's spectral cut-off `sbCut μ a = (d s ℓ)⁻¹` at the parameters
`d = X⁶`, `s = X`, `ℓ = a·X^{-163}`, `X = (μa³)^{1/323}`, satisfies the
**critical-scale bound**

    (sbCut μ a)³ ≤ μ      whenever  μ a³ ≤ 1 .

This is the exact counterpart of `Work.BoseFixB1S.sbCut_cube_mul_le` with the
*volume* `V` replaced by the diluteness `μ`: the closed form
`(sbCut μ a)³ = a⁻³·X^{468} = μ·(μa³)^{145/323}` (`Work.BoseB1Cube.sbCutCubeMul`
is the same identity multiplied by `a`) together with `μa³ ≤ 1` gives

    (sbCut μ a)³ = μ · (μa³)^{145/323} ≤ μ · 1 = μ .

It is the statement that the spectral cut-off is at most the chemical potential
to the one third, i.e. `sbCut ≤ μ^{1/3}`, which is what makes the cut-off
`c` comparable to `μ^{1/3}` in the small-box bookkeeping.
-/

namespace Work.BoseB1Cube

open Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The exact cube of FS's spectral cut-off.**  For `0 < a`, `0 < μ`,

    (sbCut μ a)³ = μ · (μa³)^{145/323} .

This holds with *no* smallness hypothesis on `μa³`: it is an identity in the
parameters.  (It is `Work.BoseB1Cube.sbCutCubeMul` divided by `a`.) -/
lemma sbCut_cube_eq_mul {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    (Work.BoseFixB1.sbCut μ a) ^ 3 = μ * fsXp (μ * a ^ 3) 145 := by
  have ht : (0 : ℝ) < μ * a ^ 3 := by positivity
  -- `fsXp t 468 = t · fsXp t 145`, since `468 = 323 + 145` and `fsXp t 323 = t`.
  have hf : fsXp (μ * a ^ 3) 468 = (μ * a ^ 3) * fsXp (μ * a ^ 3) 145 := by
    rw [show (468 : ℝ) = 323 + 145 by norm_num, ← fsXp_mul ht 323 145,
      ← delta_eq_fsXp ht.le]
  rw [Work.BoseFixB1S.sbCut_cube_eq ha hμ,
    show (Work.BoseBox.paramsAt μ a).X = fsXp (μ * a ^ 3) 1 from rfl,
    fsXp_pow ht.le]
  norm_num
  rw [hf]
  field_simp

/-- **The critical-scale bound**: `(sbCut μ a)³ ≤ μ` for `μ a³ ≤ 1`. -/
theorem sbCut_cube_le_mu {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (ht : μ * a ^ 3 ≤ 1) :
    (Work.BoseFixB1.sbCut μ a) ^ 3 ≤ μ := by
  have ht0 : (0 : ℝ) < μ * a ^ 3 := by positivity
  calc (Work.BoseFixB1.sbCut μ a) ^ 3 = μ * fsXp (μ * a ^ 3) 145 :=
        sbCut_cube_eq_mul hμ ha
    _ ≤ μ * 1 := mul_le_mul_of_nonneg_left (fsXp_le_one ht0 ht (by norm_num)) hμ.le
    _ = μ := by ring

end Work.BoseB1Cube
