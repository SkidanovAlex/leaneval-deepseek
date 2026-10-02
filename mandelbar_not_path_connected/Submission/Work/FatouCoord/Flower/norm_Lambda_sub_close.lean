import Mathlib
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Flower.norm_log_sub_log_sub_log_div_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Flower

/-- `Λ = log (-·) + π i` is `1/2`-Hölder-continuous with constant `2` near a nonzero point:
if `‖v - u‖ ≤ ‖u‖/2` then the branch defect of `log` contributes at most `2π` on top of the
elementary bound `‖log (1 + z)‖ ≤ (3/2)‖z‖` valid for `‖z‖ ≤ 1/2`. -/
theorem norm_Lambda_sub_close {u v : ℂ} (hu : u ≠ 0) (h : ‖v - u‖ ≤ ‖u‖ / 2) :
    ‖Work.FatouCoord.Petal.Lambda v - Work.FatouCoord.Petal.Lambda u‖ ≤ 2 * ‖v - u‖ / ‖u‖ + 2 * Real.pi := by
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv : v ≠ 0 := by
    intro hv0
    rw [hv0, zero_sub, norm_neg] at h
    linarith
  -- the additive constant `π i` cancels
  have hkey : Work.FatouCoord.Petal.Lambda v - Work.FatouCoord.Petal.Lambda u
      = Complex.log (-v) - Complex.log (-u) := by
    simp only [Work.FatouCoord.Petal.Lambda]
    ring
  rw [hkey]
  -- the branch defect: `log (-v) - log (-u)` differs from `log ((-v)/(-u)) = log (v/u)` by `≤ 2π`
  have hdiv : (-v) / (-u) = v / u := by
    rw [neg_div_neg_eq]
  have hb : ‖Complex.log (-v) - Complex.log (-u) - Complex.log (v / u)‖ ≤ 2 * Real.pi := by
    have := norm_log_sub_log_sub_log_div_le (a := -v) (b := -u) (neg_ne_zero.mpr hv) (neg_ne_zero.mpr hu)
    rwa [hdiv] at this
  -- `v/u = 1 + (v-u)/u` is close to `1`
  have hz : ‖(v - u) / u‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hun]
    linarith
  have hvu : v / u = 1 + (v - u) / u := by
    rw [show v = u + (v - u) by ring, add_div, div_self hu]
    ring
  have hlog : ‖Complex.log (v / u)‖ ≤ 2 * ‖v - u‖ / ‖u‖ := by
    rw [hvu]
    refine (Complex.norm_log_one_add_half_le_self hz).trans ?_
    rw [norm_div]
    have hnn : 0 ≤ ‖v - u‖ / ‖u‖ := div_nonneg (norm_nonneg _) hun.le
    rw [show 2 * ‖v - u‖ / ‖u‖ = 2 * (‖v - u‖ / ‖u‖) by ring]
    linarith
  calc ‖Complex.log (-v) - Complex.log (-u)‖
      = ‖Complex.log (v / u)
          + (Complex.log (-v) - Complex.log (-u) - Complex.log (v / u))‖ := by ring_nf
    _ ≤ ‖Complex.log (v / u)‖
          + ‖Complex.log (-v) - Complex.log (-u) - Complex.log (v / u)‖ := norm_add_le _ _
    _ ≤ 2 * ‖v - u‖ / ‖u‖ + 2 * Real.pi := add_le_add hlog hb

end Work.FatouCoord.Flower
