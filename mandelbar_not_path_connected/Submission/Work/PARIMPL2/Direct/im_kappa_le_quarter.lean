import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- The imaginary part of `τ - h1/τ` is bounded by `1/4` under the smallness hypotheses
`himτ : |τ.im| ≤ A * lam^2`, `himh1 : |h1.im| ≤ A * lam`, `64 * A ≤ R`, `lam * R^2 ≤ 1`
and `R ≥ 128`, together with `‖τ‖ = 1` and `‖h1‖ ≤ R/64`. -/
theorem im_kappa_le_quarter (A R lam : ℝ) (hA : 0 ≤ A) (hlam : 0 ≤ lam) (hR : 128 ≤ R)
    (hA64 : 64 * A ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (τ h1 : ℂ) (hτ : ‖τ‖ = 1) (hh1 : ‖h1‖ ≤ R / 64)
    (himτ : |τ.im| ≤ A * lam ^ 2) (himh1 : |h1.im| ≤ A * lam) :
    |(τ - h1 / τ).im| ≤ 1 / 4 := by
  -- Since `‖τ‖ = 1`, one has `normSq τ = 1`.
  have hnsq : Complex.normSq τ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hτ]; norm_num
  -- Exact formula for the imaginary part.
  have him : (τ - h1 / τ).im = τ.im * (1 + h1.re) - h1.im * τ.re := by
    rw [Complex.sub_im, Complex.div_im, hnsq]
    ring
  -- Coordinate bounds.
  have hreτ : |τ.re| ≤ 1 := by
    have h := Complex.abs_re_le_norm τ
    rw [hτ] at h; exact h
  have hreh1 : |h1.re| ≤ R / 64 := le_trans (Complex.abs_re_le_norm h1) hh1
  have h1re : |1 + h1.re| ≤ 1 + R / 64 := by
    have h := abs_add_le (1 : ℝ) h1.re
    rw [abs_one] at h
    linarith
  have hAlam : 0 ≤ A * lam := mul_nonneg hA hlam
  have hAlam2 : 0 ≤ A * lam ^ 2 := mul_nonneg hA (sq_nonneg lam)
  have hterm1 : |τ.im| * |1 + h1.re| ≤ A * lam ^ 2 * (1 + R / 64) :=
    mul_le_mul himτ h1re (abs_nonneg _) hAlam2
  have hterm2 : |h1.im| * |τ.re| ≤ A * lam := by
    have h := mul_le_mul himh1 hreτ (abs_nonneg _) hAlam
    simpa using h
  calc |(τ - h1 / τ).im| = |τ.im * (1 + h1.re) - h1.im * τ.re| := by rw [him]
    _ ≤ |τ.im * (1 + h1.re)| + |h1.im * τ.re| := by
          rw [sub_eq_add_neg, ← abs_neg (h1.im * τ.re)]
          exact abs_add_le _ _
    _ = |τ.im| * |1 + h1.re| + |h1.im| * |τ.re| := by rw [abs_mul, abs_mul]
    _ ≤ A * lam ^ 2 * (1 + R / 64) + A * lam := add_le_add hterm1 hterm2
    _ ≤ 1 / 4 := by
          nlinarith [sq_nonneg (R - 128), hA, hlam, hR, hA64, hlamR, mul_nonneg hA hlam,
            mul_nonneg hA (sq_nonneg lam), mul_nonneg hlam (sq_nonneg R),
            mul_nonneg hA (mul_nonneg hlam (sq_nonneg R))]

end Work.PARIMPL2.Direct
