/-
# `cuspInvInner` is invariant under a `2πℤ` shift of the angle coordinate

`cuspInvInner v q` (`Work.Cusp.Basic`) reads the polar coordinates `q = (r,θ,w₁,w₂)` and recovers
`y = invY v (w)`, the perimeter coordinate `u = (θ − 2π⟪cuspY v y, σ_v⟫/‖σ_v‖²)/(2π)` and the layer
parameter `t` from `r` and the ceiling `β (cuspX v u y)`, returning `(t • bndOfU u, y)`.

The recovered data depend on `θ` only through `u`, and every ingredient is invariant under
`u ↦ u + m` (`m : ℤ`):

* `bndOfU` is `1`-periodic (`bndOfU_add_int`),
* the ceiling is unchanged: `cuspX v (u+m) y = cuspX v u y + m σ_v`, and `σ_v` is a period of `β`
  (`beta_add_smul_slope`),
* the radial branch depends on `u` only through the ceiling.

Hence `cuspInvInner` is invariant under `θ ↦ θ + 2πm`, which is the form in which the shifted polar
chart `ThetaPolarS` (whose angle coordinate is the `c`-shifted lift `uS c p = u p − ⌊u p − c⌋`,
differing from `u p` by an integer) meets the unshifted one.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.bndOfU_add_int
import Submission.Work.Cusp.beta_add_smul_slope
import Submission.Work.Cusp.invY_wOf
import Submission.Work.Cusp.wOf_invY
import Submission.Work.Cusp.slope_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

open scoped Real InnerProductSpace

noncomputable section

/-- **`cuspInvInner` only sees `(q 0, q 1, q 2, q 3)` through `q 0`, the pair `(q 2, q 3)` and
`q 1` up to an integer multiple of `2π`.**  If `q` and `q'` have the same first coordinate and the
same pair of `w`-coordinates, and `q 1 = q' 1 + 2πm` with `m : ℤ`, then `cuspInvInner` takes the
same value on them: the recovered perimeter coordinates differ by the integer `m`, which is
invisible to `bndOfU` and to the ceiling `β (cuspX v · y)`. -/
private lemma cuspInvInner_congr (v : Fin 5) (m : ℤ) (q q' : E4)
    (h0 : q 0 = q' 0)
    (hy : (!₂[q 2, q 3] : E2) = (!₂[q' 2, q' 3] : E2))
    (h1 : q 1 = q' 1 + (m : ℝ) * (2 * π)) :
    cuspInvInner v q = cuspInvInner v q' := by
  simp only [cuspInvInner]
  rw [h0, hy, h1]
  set y : E2 := invY v !₂[q' 2, q' 3] with hydef
  rw [show (q' 1 + (m : ℝ) * (2 * π) - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π)
      = (q' 1 - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π) + (m : ℝ) from by
        field_simp
        ring]
  set U : ℝ := (q' 1 - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π) with hUdef
  have hbeta : beta (cuspX v (U + (m : ℝ)) y) = beta (cuspX v U y) := by
    have hcx : cuspX v (U + (m : ℝ)) y = cuspX v U y + (m : ℝ) • slope v := by
      rw [cuspX, cuspX, add_smul]
      abel
    rw [hcx, beta_add_smul_slope]
  rw [bndOfU_add_int, hbeta]

/-- **`cuspInvInner` is invariant under adding `2πm` (`m : ℤ`) to the angle coordinate.** -/
theorem cuspInvInner_add_int_mul_two_pi (v : Fin 5) (m : ℤ) (r θ : ℝ) (w : E2) :
    cuspInvInner v (!₂[r, θ + (m : ℝ) * (2 * π), w 0, w 1] : E4)
      = cuspInvInner v (!₂[r, θ, w 0, w 1] : E4) := by
  refine cuspInvInner_congr v m _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · show θ + (m : ℝ) * (2 * π) = θ + (m : ℝ) * (2 * π)
    rfl

end

end Work.Cusp
