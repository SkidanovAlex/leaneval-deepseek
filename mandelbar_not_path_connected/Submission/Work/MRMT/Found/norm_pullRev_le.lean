/-
Work.MRMT.Found — the elementary norm bound for the pull-back coefficient `pullRev`.

`pullRev μ f z` is the complex dilatation of the orientation-reversing composite
`star ∘ F ∘ f` (see `conjAux.lean`): writing `a = ∂f z`, `b = ∂̄f z`, `m = μ (f z)`,

`pullRev μ f z = (star a + star m · b) / (star b + star m · a)`.

At a point where `f` is *antiholomorphic* (`a = ∂f z = 0`) this degenerates to
`star m · b / star b`, whose modulus is at most `‖m‖` because the factor `b / star b` has
modulus at most one (and is `0` when `b = 0`).  This is the estimate that lets one bound the
pull-back dilatation of a reversing composite by the dilatation of the map at the image point.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- `‖(star m * b) / star b‖ ≤ ‖m‖` for complex `m`, `b`: the quotient `b / star b` has modulus
at most one, and is `0` in the degenerate case `b = 0` (where also `star b = 0`). -/
theorem norm_star_mul_div_star_le (m b : ℂ) : ‖star m * b / star b‖ ≤ ‖m‖ := by
  rcases eq_or_ne b 0 with hb | hb
  · subst hb; simp
  · rw [norm_div, norm_mul, norm_star, norm_star,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hb)]

theorem norm_pullRev_le {μ f : ℂ → ℂ} {z : ℂ} (hz : Work.MRMT.dz f z = 0) :
    ‖Work.MRMT.Found.pullRev μ f z‖ ≤ ‖μ (f z)‖ := by
  have hb : ‖star (μ (f z)) * Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z)‖ ≤ ‖μ (f z)‖ :=
    norm_star_mul_div_star_le _ _
  convert hb using 2
  simp only [Work.MRMT.Found.pullRev, hz, star_zero, zero_add, mul_zero, add_zero]

end Work.MRMT.Found
