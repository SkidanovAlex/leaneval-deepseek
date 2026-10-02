import Mathlib
import Submission.Work.SeedCertRay.Disk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- **A disk inside an open half-plane, from a margin condition.**

If the rational margin `p * D.cx + q * D.cy` of the centre of the disk in the direction `(p, q)`
strictly exceeds `(|p| + |q|) * D.r`, then the whole disk lies in the open half-plane `{p x + q y > 0}`.

For `z ∈ D` write `w = z - D.center`; then `‖w‖ ≤ D.r`, so
`|p * w.re + q * w.im| ≤ (|p| + |q|) * D.r`, and
`p * z.re + q * z.im = (p * D.cx + q * D.cy) + (p * w.re + q * w.im) ≥ margin - (|p| + |q|) * D.r > 0`. -/
theorem disk_mem_halfplane (D : Work.SeedCertRay.Disk) (p q : ℚ) (h : (|p| + |q|) * D.r < p * D.cx + q * D.cy) : D.toSet ⊆ Work.SeedCertRay.halfplane (p, q) := by
  intro z hz
  rw [Disk.mem_toSet] at hz
  have hz' : ‖z - D.center‖ ≤ (D.r : ℝ) := hz
  set w : ℂ := z - D.center with hw
  have hre : |w.re| ≤ (D.r : ℝ) := le_trans (Complex.abs_re_le_norm w) hz'
  have him : |w.im| ≤ (D.r : ℝ) := le_trans (Complex.abs_im_le_norm w) hz'
  -- The linear part `p * w.re + q * w.im` is bounded below by `-((|p| + |q|) * D.r)`.
  have hbnd : -((|p| : ℝ) + (|q| : ℝ)) * (D.r : ℝ) ≤ (p : ℝ) * w.re + (q : ℝ) * w.im := by
    have hp1 : |(p : ℝ) * w.re| ≤ (|p| : ℝ) * (D.r : ℝ) := by
      rw [abs_mul, ← Rat.cast_abs]
      exact mul_le_mul_of_nonneg_left hre (by positivity)
    have hq1 : |(q : ℝ) * w.im| ≤ (|q| : ℝ) * (D.r : ℝ) := by
      rw [abs_mul, ← Rat.cast_abs]
      exact mul_le_mul_of_nonneg_left him (by positivity)
    linarith [neg_abs_le ((p : ℝ) * w.re), neg_abs_le ((q : ℝ) * w.im), hp1, hq1]
  -- The hypothesis, transported to `ℝ`.
  have hR : ((|p| : ℝ) + (|q| : ℝ)) * (D.r : ℝ) < (p : ℝ) * (D.cx : ℝ) + (q : ℝ) * (D.cy : ℝ) := by
    have hcast : (((|p| : ℚ) : ℝ) + ((|q| : ℚ) : ℝ)) * (D.r : ℝ) <
        (p : ℝ) * (D.cx : ℝ) + (q : ℝ) * (D.cy : ℝ) := by
      exact_mod_cast h
    simpa using hcast
  have hzre : z.re = (D.cx : ℝ) + w.re := by
    have hzc : z = D.center + w := by simp [w]
    rw [hzc, Complex.add_re]
    simp [Disk.center]
  have hzim : z.im = (D.cy : ℝ) + w.im := by
    have hzc : z = D.center + w := by simp [w]
    rw [hzc, Complex.add_im]
    simp [Disk.center]
  have hgoal : 0 < (p : ℝ) * z.re + (q : ℝ) * z.im := by
    rw [hzre, hzim]
    nlinarith [hbnd, hR]
  simpa [Work.SeedCertRay.halfplane] using hgoal

end Work.SeedCertRay
