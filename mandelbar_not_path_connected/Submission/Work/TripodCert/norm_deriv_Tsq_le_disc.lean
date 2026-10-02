import Mathlib
import Submission.Work.TripodCert.UniqueDefs
import Submission.Work.SeedDyn.deriv_Tsq_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

/-- **The derivative bound on the disc `E`.**  For a parameter `c` of the parameter box `Xb` and
for `w` in the closed disc of radius `UREq` about `z₀`, the derivative of the holomorphic second
iterate `Tsq c z = (z² + c̄)² + c` is bounded by the rational constant `ULq`:

`deriv (Tsq c) w = 4 w (w² + c̄)`, so with `‖w‖ ≤ UMq` and
`‖w² + c̄‖ ≤ ‖z₀² + c̄₀‖ + ‖c - c₀‖ + ‖w - z₀‖ ‖w + z₀‖ ≤ US0q + UDcq + 2 UMq UREq`
the product is at most `ULq = 4 UMq (US0q + UDcq + 2 UMq UREq)`. -/
theorem norm_deriv_Tsq_le_disc {c : ℂ} (hc : Work.SeedCertRay.Xb.mem c) {w : ℂ}
    (hw : ‖w - Work.TripodCert.uZ0‖ ≤ (Work.TripodCert.UREq : ℝ)) :
    ‖deriv (Work.Landing.Tsq c) w‖ ≤ (Work.TripodCert.ULq : ℝ) := by
  have hUMq_nn : (0 : ℝ) ≤ (UMq : ℝ) := by norm_num [UMq]
  have hUREq_nn : (0 : ℝ) ≤ (UREq : ℝ) := by norm_num [UREq]
  have hUL : (ULq : ℝ)
      = 4 * (UMq : ℝ) * ((US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ)) := by
    rw [ULq]; push_cast; ring
  -- `‖w‖ ≤ UMq`
  have hwUM : ‖w‖ ≤ (UMq : ℝ) := by
    have h1 : ‖w‖ ≤ ‖uZ0‖ + ‖w - uZ0‖ := by
      calc ‖w‖ = ‖uZ0 + (w - uZ0)‖ := by congr 1; ring
        _ ≤ ‖uZ0‖ + ‖w - uZ0‖ := norm_add_le _ _
    linarith [hUMe, hw]
  have hz0UM : ‖uZ0‖ ≤ (UMq : ℝ) := by linarith [hUMe, hUREq_nn]
  -- the quadratic factor
  have hfac : ‖w ^ 2 + star c‖
      ≤ (US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ) := by
    have hdecomp : w ^ 2 + star c
        = (uZ0 ^ 2 + star c0T) + ((w - uZ0) * (w + uZ0)) + (star c - star c0T) := by ring
    rw [hdecomp]
    have h1 := hUS0
    have h2 : ‖(w - uZ0) * (w + uZ0)‖ ≤ 2 * (UMq : ℝ) * (UREq : ℝ) := by
      rw [norm_mul]
      have hplus : ‖w + uZ0‖ ≤ 2 * (UMq : ℝ) := by
        have := norm_add_le w uZ0
        linarith [hwUM, hz0UM]
      calc ‖w - uZ0‖ * ‖w + uZ0‖ ≤ (UREq : ℝ) * (2 * (UMq : ℝ)) :=
            mul_le_mul hw hplus (norm_nonneg _) hUREq_nn
        _ = 2 * (UMq : ℝ) * (UREq : ℝ) := by ring
    have h3 : ‖star c - star c0T‖ ≤ (UDcq : ℝ) := by
      rw [← star_sub, norm_star]
      exact hDc hc
    have htri : ‖(uZ0 ^ 2 + star c0T) + ((w - uZ0) * (w + uZ0)) + (star c - star c0T)‖
        ≤ ‖uZ0 ^ 2 + star c0T‖ + ‖(w - uZ0) * (w + uZ0)‖ + ‖star c - star c0T‖ := by
      calc ‖(uZ0 ^ 2 + star c0T) + ((w - uZ0) * (w + uZ0)) + (star c - star c0T)‖
          ≤ ‖(uZ0 ^ 2 + star c0T) + ((w - uZ0) * (w + uZ0))‖ + ‖star c - star c0T‖ :=
            norm_add_le _ _
        _ ≤ (‖uZ0 ^ 2 + star c0T‖ + ‖(w - uZ0) * (w + uZ0)‖) + ‖star c - star c0T‖ := by
            gcongr; exact norm_add_le _ _
    linarith
  have hstep : ‖w‖ * ‖w ^ 2 + star c‖
      ≤ (UMq : ℝ) * ((US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ)) :=
    mul_le_mul hwUM hfac (norm_nonneg _) hUMq_nn
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [Work.SeedDyn.deriv_Tsq_eq, hUL]
  calc ‖(4 : ℂ) * w * (w ^ 2 + star c)‖
      = 4 * (‖w‖ * ‖w ^ 2 + star c‖) := by rw [norm_mul, norm_mul, h4]; ring
    _ ≤ 4 * ((UMq : ℝ) * ((US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 4 * (UMq : ℝ) * ((US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ)) := by ring

end Work.TripodCert
