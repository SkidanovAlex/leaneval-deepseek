import Mathlib
import Submission.Work.SeedCertRay.Disk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- Every point of a rational box `B` is within the rational radius `B.rad` of the rational
centre `B.center`.  (Local copy of `Work.SeedCertRay.norm_sub_center_le`, kept here so that the
present file depends only on `Mathlib` and `Disk`.) -/
private theorem box_norm_sub_center_le (B : Work.SeedCertRay.Box) {z : ℂ} (hz : B.mem z) :
    ‖z - B.center‖ ≤ ((B.rad : ℚ) : ℝ) := by
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

theorem disk_mem_hZl (D : Work.SeedCertRay.Disk) (X : Work.SeedCertRay.Box) (s : ℚ) (hs : 0 ≤ s) (h : ((s ^ 2 + D.r + X.rad : ℚ) : ℝ) ^ 2 ≤ (D.cx - X.center.re) ^ 2 + (D.cy - X.center.im) ^ 2) : ∀ z c : ℂ, D.mem z → X.mem c → (s : ℝ) ^ 2 ≤ ‖z - c‖ := by
  -- The two centres, as points of `ℂ`.
  have hDcom : D.center - X.center
      = ((D.cx : ℝ) - X.center.re : ℂ) + ((D.cy : ℝ) - X.center.im : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp [Disk.center, Box.center, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  -- The squared distance of the two centres is exactly the right-hand side of `h`.
  have hsq : ‖D.center - X.center‖ ^ 2
      = (D.cx - X.center.re) ^ 2 + (D.cy - X.center.im) ^ 2 := by
    rw [hDcom, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
    ring
  -- Hence `h` gives `a ≤ ‖Dcenter - Xcenter‖` for `a = s^2 + D.r + X.rad`.
  have ha2 : ((s ^ 2 + D.r + X.rad : ℚ) : ℝ) ^ 2 ≤ ‖D.center - X.center‖ ^ 2 := by
    rw [hsq]; exact h
  have ha_le : ((s ^ 2 + D.r + X.rad : ℚ) : ℝ) ≤ ‖D.center - X.center‖ := by
    have h1 : |((s ^ 2 + D.r + X.rad : ℚ) : ℝ)| ≤ ‖D.center - X.center‖ := by
      have h2 := sq_le_sq.mp ha2
      rwa [abs_of_nonneg (norm_nonneg _)] at h2
    exact le_trans (le_abs_self _) h1
  intro z c hz hc
  have hzc : ‖z - D.center‖ ≤ (D.r : ℝ) := hz
  have hcc : ‖c - X.center‖ ≤ ((X.rad : ℚ) : ℝ) := box_norm_sub_center_le X hc
  -- Triangle inequality: the two centres are no farther apart than the sum of the three pieces.
  have htri : ‖D.center - X.center‖ ≤ ‖z - c‖ + (D.r : ℝ) + ((X.rad : ℚ) : ℝ) := by
    have hdec : D.center - X.center = (z - c) + (D.center - z) + (c - X.center) := by ring
    rw [hdec]
    calc ‖(z - c) + (D.center - z) + (c - X.center)‖
        ≤ ‖(z - c) + (D.center - z)‖ + ‖c - X.center‖ := norm_add_le _ _
      _ ≤ (‖z - c‖ + ‖D.center - z‖) + ‖c - X.center‖ := by
            linarith [norm_add_le (z - c) (D.center - z)]
      _ ≤ (‖z - c‖ + (D.r : ℝ)) + ((X.rad : ℚ) : ℝ) := by
            have h1 : ‖D.center - z‖ = ‖z - D.center‖ := norm_sub_rev _ _
            rw [h1]; linarith
      _ = ‖z - c‖ + (D.r : ℝ) + ((X.rad : ℚ) : ℝ) := by ring
  have hmain : ((s ^ 2 + D.r + X.rad : ℚ) : ℝ) ≤ ‖z - c‖ + (D.r : ℝ) + ((X.rad : ℚ) : ℝ) :=
    le_trans ha_le htri
  have hcast : ((s ^ 2 + D.r + X.rad : ℚ) : ℝ)
      = (s : ℝ) ^ 2 + (D.r : ℝ) + ((X.rad : ℚ) : ℝ) := by push_cast; ring
  linarith [hmain, hcast]

end Work.SeedCertRay
