import Mathlib
import Submission.Work.SeedCertRay.Disk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- **The disk-around-`conj w0` certificate.**  If the reflected point `conj (w0re + w0im·i)` is at
squared distance at most `(E.r - ρ)^2` from the centre of the disk `E` (with `ρ ≤ E.r`), then the
whole closed disk of radius `ρ` about `conj (w0re + w0im·i)` is contained in `E`.  This is the
triangle inequality `‖u - centre‖ ≤ ‖u - conj w0‖ + ‖conj w0 - centre‖ ≤ ρ + (E.r - ρ) = E.r`,
together with the elementary identity relating the real coordinates to the complex norm. -/
theorem disk_mem_hE (E : Work.SeedCertRay.Disk) (w0re w0im ρ : ℚ) (hρ : 0 ≤ ρ) (hρr : ρ ≤ E.r) (h : (w0re - E.cx) ^ 2 + (-w0im - E.cy) ^ 2 ≤ (E.r - ρ) ^ 2) : ∀ u : ℂ, ‖u - starRingEnd ℂ (((w0re : ℝ) : ℂ) + ((w0im : ℝ) : ℂ) * Complex.I)‖ ≤ (ρ : ℝ) → E.mem u := by
  intro u hu
  -- `w` is the reflected point `conj (w0re + w0im·i) = w0re - w0im·i`.
  set w : ℂ := starRingEnd ℂ (((w0re : ℝ) : ℂ) + ((w0im : ℝ) : ℂ) * Complex.I) with hw
  -- The squared distance from `w` to the centre, in real coordinates.
  have hsq : ‖w - E.center‖ ^ 2 = (((w0re - E.cx) ^ 2 + (-w0im - E.cy) ^ 2 : ℚ) : ℝ) := by
    rw [hw, Complex.sq_norm, Complex.normSq_apply]
    simp [Disk.center, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have hcast : (((E.r - ρ) ^ 2 : ℚ) : ℝ) = ((E.r - ρ : ℚ) : ℝ) ^ 2 := by push_cast; ring
  -- `E.r - ρ ≥ 0` is what lets us take the square root of the hypothesis.
  have hr0 : (0:ℝ) ≤ ((E.r - ρ : ℚ) : ℝ) := by
    have : ((ρ:ℚ):ℝ) ≤ ((E.r:ℚ):ℝ) := by exact_mod_cast hρr
    push_cast
    linarith
  -- Hence `‖w - E.center‖ ≤ E.r - ρ`.
  have hdle : ‖w - E.center‖ ≤ ((E.r - ρ : ℚ) : ℝ) := by
    have h1 : ‖w - E.center‖ ^ 2 ≤ ((E.r - ρ : ℚ) : ℝ) ^ 2 := by
      rw [hsq, ← hcast]
      exact_mod_cast h
    have h2 := sq_le_sq.mp h1
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hr0] at h2
  have hcastr : ((E.r - ρ : ℚ) : ℝ) = (E.r : ℝ) - (ρ : ℝ) := by push_cast; ring
  -- Triangle inequality through `w`.
  show ‖u - E.center‖ ≤ (E.r : ℝ)
  have htri : ‖u - E.center‖ ≤ ‖u - w‖ + ‖w - E.center‖ := by
    have he : u - E.center = (u - w) + (w - E.center) := by ring
    rw [he]; exact norm_add_le _ _
  linarith [htri, hu, hdle, hcastr]

end Work.SeedCertRay
