/-
# SeedCertRay — the disk-to-box drift estimate of the certified ray chain

`disk_sub_box_normSq_le` is the **geometric drift estimate** used by the certificate
generator: it converts the *centre* inequality

  `‖(D.center - X.center) - w₀ ^ 2‖ ≤ M - (D.r + X.rad)`

into the *pointwise* drift hypothesis

  `‖(z - c) - w₀ ^ 2‖ ^ 2 ≤ M ^ 2`   for all `z ∈ D`, `c ∈ X`

consumed by `diskCover_of_bounds` / `diskCover_of_bounds_sharp` (there with
`w0re, w0im, M` rational and `M ≥ D.r + X.rad`).

The mathematics is one triangle inequality.  Writing

* `A := (D.center - X.center) - w₀ ^ 2`,
* `B := (z - D.center) + (X.center - c)`,

we have `(z - c) - w₀ ^ 2 = A + B`, `‖A‖ ≤ M - (D.r + X.rad)` (from the hypothesis, read
coordinatewise: `A.re` and `A.im` are exactly the two bracket terms of `h`), and
`‖B‖ ≤ ‖z - D.center‖ + ‖X.center - c‖ ≤ D.r + X.rad` (the second summand is
`norm_sub_center_le`).  Hence `‖(z - c) - w₀ ^ 2‖ ≤ M`, and squaring (with `M ≥ 0`) gives the
claim.
-/
import Mathlib
import Submission.Work.SeedCertRay.Disk
import Submission.Work.SeedCertRay.norm_sub_center_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.SeedCertRay

open Classical Set Function Filter
open scoped Topology ComplexConjugate

/-- `(a + i b) ^ 2 = (a ^ 2 - b ^ 2) + i (2 a b)` for real `a`, `b`. -/
private lemma ofReal_add_I_mul_sq (a b : ℝ) :
    (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I) ^ 2
      = (((a ^ 2 - b ^ 2 : ℝ)) : ℂ) + (((2 * a * b : ℝ)) : ℂ) * Complex.I := by
  rw [pow_two]
  simp only [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    sub_zero]
  constructor <;> ring

theorem disk_sub_box_normSq_le (D : Work.SeedCertRay.Disk) (X : Work.SeedCertRay.Box) (w0re w0im M : ℚ) (hM : 0 ≤ M) (hMr : ((D.r + X.rad : ℚ) : ℝ) ≤ (M : ℝ)) (h : ((D.cx - X.center.re) - (w0re ^ 2 - w0im ^ 2)) ^ 2 + ((D.cy - X.center.im) - 2 * w0re * w0im) ^ 2 ≤ (M - ((D.r + X.rad : ℚ) : ℝ)) ^ 2) : ∀ z c : ℂ, D.mem z → X.mem c → ‖(z - c) - (((w0re : ℝ) : ℂ) + ((w0im : ℝ) : ℂ) * Complex.I) ^ 2‖ ^ 2 ≤ (M : ℝ) ^ 2 := by
  intro z c hz hc
  set w : ℂ := ((w0re : ℝ) : ℂ) + ((w0im : ℝ) : ℂ) * Complex.I with hw
  set A : ℂ := (D.center - X.center) - w ^ 2 with hA
  set B : ℂ := (z - D.center) + (X.center - c) with hB
  -- Numeric forms of the hypotheses.
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hρM : ((D.r : ℚ) : ℝ) + ((X.rad : ℚ) : ℝ) ≤ (M : ℝ) := by
    have hh := hMr
    push_cast at hh
    exact hh
  have hcanon : ((D.cx : ℝ) - X.center.re - ((w0re : ℝ) ^ 2 - (w0im : ℝ) ^ 2)) ^ 2
      + ((D.cy : ℝ) - X.center.im - 2 * (w0re : ℝ) * (w0im : ℝ)) ^ 2
      ≤ ((M : ℝ) - (((D.r : ℚ) : ℝ) + ((X.rad : ℚ) : ℝ))) ^ 2 := by
    have hh := h
    push_cast at hh
    exact hh
  -- The decomposition at the heart of the estimate.
  have hsum : (z - c) - w ^ 2 = A + B := by
    rw [hA, hB]
    ring
  -- Coordinates of `A`.
  have hAre : A.re = (D.cx : ℝ) - X.center.re - ((w0re : ℝ) ^ 2 - (w0im : ℝ) ^ 2) := by
    rw [hA, hw, ofReal_add_I_mul_sq]
    simp only [Complex.sub_re, Disk.center, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
    ring
  have hAim : A.im = (D.cy : ℝ) - X.center.im - 2 * (w0re : ℝ) * (w0im : ℝ) := by
    rw [hA, hw, ofReal_add_I_mul_sq]
    simp only [Complex.sub_im, Disk.center, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
    ring
  -- `‖A‖ ≤ M - (D.r + X.rad)`.
  have hAsq : ‖A‖ ^ 2 ≤ ((M : ℝ) - (((D.r : ℚ) : ℝ) + ((X.rad : ℚ) : ℝ))) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hAre, hAim]
    nlinarith [hcanon]
  have hAρ : 0 ≤ (M : ℝ) - (((D.r : ℚ) : ℝ) + ((X.rad : ℚ) : ℝ)) := by linarith
  have hAnorm : ‖A‖ ≤ (M : ℝ) - (((D.r : ℚ) : ℝ) + ((X.rad : ℚ) : ℝ)) := by
    calc ‖A‖ = Real.sqrt (‖A‖ ^ 2) := (Real.sqrt_sq (norm_nonneg A)).symm
      _ ≤ Real.sqrt (((M : ℝ) - (((D.r : ℚ) : ℝ) + ((X.rad : ℚ) : ℝ))) ^ 2) :=
            Real.sqrt_le_sqrt hAsq
      _ = (M : ℝ) - (((D.r : ℚ) : ℝ) + ((X.rad : ℚ) : ℝ)) := Real.sqrt_sq hAρ
  -- `‖B‖ ≤ D.r + X.rad`.
  have hBnorm : ‖B‖ ≤ ((D.r : ℚ) : ℝ) + ((X.rad : ℚ) : ℝ) := by
    rw [hB]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖z - D.center‖ ≤ ((D.r : ℚ) : ℝ) := hz
    have h2 : ‖X.center - c‖ ≤ ((X.rad : ℚ) : ℝ) := by
      rw [norm_sub_rev]
      exact norm_sub_center_le X hc
    linarith
  -- Conclusion.
  have hnorm : ‖(z - c) - w ^ 2‖ ≤ (M : ℝ) := by
    rw [hsum]
    calc ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
      _ ≤ ((M : ℝ) - (((D.r : ℚ) : ℝ) + ((X.rad : ℚ) : ℝ)))
            + (((D.r : ℚ) : ℝ) + ((X.rad : ℚ) : ℝ)) := add_le_add hAnorm hBnorm
      _ = (M : ℝ) := by ring
  nlinarith [hnorm, hM0, norm_nonneg ((z - c) - w ^ 2)]

end Work.SeedCertRay
