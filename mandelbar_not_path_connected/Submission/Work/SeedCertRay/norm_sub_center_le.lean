import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- A point of a rational box is within the rational radius `B.rad = (xh - xl) + (yh - yl)` of
the rational centre `B.center`.  (The bound is not sharp -- the sharp bound is half the
diagonal `½√((xh-xl)² + (yh-yl)²)` -- but it is rational and adequate for the certificate.) -/
theorem norm_sub_center_le (B : Work.SeedCertRay.Box) {z : ℂ} (hz : B.mem z) : ‖z - B.center‖ ≤ ((B.rad : ℚ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hcre : (B.center).re = ((B.xl : ℝ) + B.xh) / 2 := by
    simp [Box.center]
  have hcim : (B.center).im = ((B.yl : ℝ) + B.yh) / 2 := by
    simp [Box.center]
  set a : ℝ := ((B.xh : ℝ) - B.xl) / 2 with ha
  set b : ℝ := ((B.yh : ℝ) - B.yl) / 2 with hb
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  have hx : |z.re - (B.center).re| ≤ a := by
    rw [hcre, ha, abs_le]
    constructor <;> linarith
  have hy : |z.im - (B.center).im| ≤ b := by
    rw [hcim, hb, abs_le]
    constructor <;> linarith
  have hsq : ‖z - B.center‖ ^ 2 =
      (z.re - (B.center).re)^2 + (z.im - (B.center).im)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hbound : ‖z - B.center‖ ^ 2 ≤ (a + b)^2 := by
    rw [hsq]
    have hxl := abs_le.mp hx
    have hyl := abs_le.mp hy
    nlinarith [hxl.1, hxl.2, hyl.1, hyl.2, ha0, hb0]
  have hnorm : ‖z - B.center‖ ≤ a + b := by
    nlinarith [hbound, norm_nonneg (z - B.center), ha0, hb0]
  have hrad : ((B.rad : ℚ) : ℝ) = 2 * a + 2 * b := by
    rw [Box.rad, ha, hb]
    push_cast
    ring
  rw [hrad]
  linarith

end Work.SeedCertRay
