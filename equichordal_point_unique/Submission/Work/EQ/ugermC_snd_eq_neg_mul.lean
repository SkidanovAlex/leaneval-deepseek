import Mathlib
import Submission.Work.EQ.DefsCore

/-! # The `W`-coordinate of a point of the mirror germ

Cleared (division-free) form of the identity `W(ugermC v) = -h v` for the meromorphic coordinate
`W(x,y) = y/(x - a/2)` of `Work.EQ.DefsCore`. -/

set_option linter.unusedVariables false

namespace Work.EQ

open Complex

/-- **The `W`-coordinate of a point of the mirror germ.**  For any `h` with `h 0 = 0` and every
`v : ℂ`, the second coordinate of the mirror germ point `ugermC a h v` satisfies
`(ugermC a h v).2 = - h v * ((ugermC a h v).1 - a/2)`.
(This is the cleared form of the identity `W (ugermC v) = -h v` for the coordinate
`W(x,y) = y/(x - a/2)`; it involves no division, so it is valid for every `v`, including those
where the denominators in `ugermC` vanish.) -/
theorem ugermC_snd_eq_neg_mul (a : ℝ) {h : ℂ → ℂ} (h0 : h 0 = 0) (v : ℂ) :
    (ugermC a h v).2 = -h v * ((ugermC a h v).1 - ((a / 2 : ℝ) : ℂ)) := by
  have key : v * dslope h 0 v = h v := by
    have h1 := sub_smul_dslope h (0 : ℂ) v
    rw [h0, sub_zero] at h1
    simpa [smul_eq_mul] using h1
  have hcast : ((a / 2 : ℝ) : ℂ) = (a : ℂ) / 2 := by push_cast; ring
  rw [hcast]
  simp only [ugermC, eqMirror, germC]
  rw [show (a : ℂ) * v * dslope h 0 v * dslope (fun v => h ((eqLam a : ℂ) * v)) 0 v
      = h v * ((a : ℂ) * dslope (fun v => h ((eqLam a : ℂ) * v)) 0 v) by rw [← key]; ring]
  ring

end Work.EQ
