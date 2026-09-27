import Mathlib
import Submission.Work.Drive.SeamSweep

/-!
# The square-to-disk map of the capped plane

`Work.Drive.diskPt` (`Submission/Work/Drive/cappedPlaneCharts.lean`) presents the capped plane
`P_u = u·M ∪ cap` as the quotient of the closed unit disk by the antipodal identification of its
boundary circle.  The parity bookkeeping of the chain route
(`Work.Drive.manifold_triple_inter_boundary_parity`, `Work.Drive.manifold_triple_seam_cancel`) needs
the plane as a **map on a cube**, with the antipodal identification of the *square's* boundary.

This file supplies the classical square-to-disk map

> `sqDisk y = (a·√(1 − b²/2), b·√(1 − a²/2))`,   `a = 2 y 0 − 1`,   `b = 2 y 1 − 1`,

cut off by a smooth bump so that it is a globally `C^∞` map `ℝ² → ℂ`.  Its two defining features are

* **oddness about the centre `(1/2,1/2)` of the square**, `sqDisk (seamInv2 y) = - sqDisk y`, so that
  the antipodal identification of the square's boundary corresponds exactly to the antipodal
  identification of the disk's boundary: `diskPt` then identifies the two images
  (`Work.Drive.planeSq_seamInv`);
* **the boundary of the square maps onto the unit circle**: `‖sqDisk y‖ = 1` exactly for `y` on the
  boundary of the square, and `‖sqDisk y‖ ≤ 1` on the square.
-/

set_option autoImplicit false

namespace Work.Drive

open scoped Topology ContDiff
open Manifold

noncomputable section

/-! ## The smooth weight `√(1 - b²/2)` on the square -/

/-- The bump that makes the square-to-disk map smooth everywhere: it is `1` on `[-1,1]` and vanishes
outside `[-7/5,7/5]`, where `1 - b²/2 ≥ 1/50 > 0`. -/
def sqBump : ContDiffBump (0 : ℝ) := ⟨6 / 5, 7 / 5, by norm_num, by norm_num⟩

@[simp] lemma sqBump_rIn : sqBump.rIn = 6 / 5 := rfl

@[simp] lemma sqBump_rOut : sqBump.rOut = 7 / 5 := rfl

lemma sqBump_apply_eq_one {b : ℝ} (hb : |b| ≤ 1) : sqBump b = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, sqBump_rIn]
  linarith

lemma sqBump_apply_eq_zero {b : ℝ} (hb : 7 / 5 ≤ |b|) : sqBump b = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [dist_zero_right, Real.norm_eq_abs, sqBump_rOut]
  exact hb

/-- **The weight of the square-to-disk map**: `√(1 - b²/2)`, cut off by the bump `sqBump` so that it
is a globally smooth function of `b`.  On `[-1,1]` it agrees with `√(1 - b²/2)`. -/
def sqWeight (b : ℝ) : ℝ := sqBump b * Real.sqrt (1 - b ^ 2 / 2)

lemma sqWeight_sq {b : ℝ} (hb : |b| ≤ 1) : sqWeight b ^ 2 = 1 - b ^ 2 / 2 := by
  have h1 : sqBump b = 1 := sqBump_apply_eq_one hb
  have h2 : 0 ≤ 1 - b ^ 2 / 2 := by
    have hle : b ^ 2 ≤ 1 := by
      have := abs_le.mp hb
      nlinarith [this.1, this.2]
    linarith
  rw [sqWeight, h1, one_mul, Real.sq_sqrt h2]

lemma sqWeight_nonneg (b : ℝ) : 0 ≤ sqWeight b :=
  mul_nonneg (ContDiffBump.nonneg sqBump) (Real.sqrt_nonneg _)

lemma sqWeight_pos {b : ℝ} (hb : |b| ≤ 1) : 0 < sqWeight b := by
  have h1 : sqBump b = 1 := sqBump_apply_eq_one hb
  have h2 : 0 < 1 - b ^ 2 / 2 := by
    have hle : b ^ 2 ≤ 1 := by
      have := abs_le.mp hb
      nlinarith [this.1, this.2]
    linarith
  rw [sqWeight, h1, one_mul]
  exact Real.sqrt_pos.mpr h2

lemma sqWeight_even (b : ℝ) : sqWeight (-b) = sqWeight b := by
  rw [sqWeight, sqWeight, ContDiffBump.neg sqBump b, neg_sq]

/-- The weight is globally smooth: it is a product of the smooth bump with the square root of
`1 - b²/2`, which is smooth wherever it is non-zero, and the bump vanishes on a neighbourhood of the
only two zeroes `±√2` of that function. -/
theorem sqWeight_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sqWeight := by
  rw [contDiff_iff_contDiffAt]
  intro b
  by_cases hb : 1 - b ^ 2 / 2 = 0
  · -- near `±√2` the bump vanishes, so the weight is locally zero
    have hb2 : b ^ 2 = 2 := by linarith
    have habs : |b| = Real.sqrt 2 := by
      rw [← Real.sqrt_sq_eq_abs, hb2]
    have hbig : 7 / 5 < |b| := by
      rw [habs]
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hev : ∀ᶠ x in 𝓝 b, sqWeight x = 0 := by
      have hc : ∀ᶠ x in 𝓝 b, 7 / 5 < |x| :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds hbig
      filter_upwards [hc] with x hx
      rw [sqWeight, sqBump_apply_eq_zero (le_of_lt hx), zero_mul]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  · -- away from `±√2` the square root is smooth
    have hcont : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => 1 - x ^ 2 / 2) b := by
      fun_prop
    exact (ContDiffBump.contDiff (n := ⊤) sqBump).contDiffAt.mul (hcont.sqrt hb)

/-! ## The square-to-disk map -/

/-- **The square-to-disk map.**  The point of the plane `ℂ` of coordinates
`(a·√(1 - b²/2), b·√(1 - a²/2))` with `a = 2 y 0 - 1`, `b = 2 y 1 - 1` (written with the smooth cut-off
weight `sqWeight` so that it extends to a globally smooth map on `ℝ²`).  It maps the unit square
`[0,1]²` onto the closed unit disk, its boundary onto the unit circle, and it is odd about the centre
of the square. -/
def sqDisk (y : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (((2 * y 0 - 1) * sqWeight (2 * y 1 - 1) : ℝ) : ℂ)
    + (((2 * y 1 - 1) * sqWeight (2 * y 0 - 1) : ℝ) : ℂ) * Complex.I

@[simp] lemma sqDisk_apply_re (y : EuclideanSpace ℝ (Fin 2)) :
    (sqDisk y).re = (2 * y 0 - 1) * sqWeight (2 * y 1 - 1) := by
  simp [sqDisk]

@[simp] lemma sqDisk_apply_im (y : EuclideanSpace ℝ (Fin 2)) :
    (sqDisk y).im = (2 * y 1 - 1) * sqWeight (2 * y 0 - 1) := by
  simp [sqDisk]

/-- The two coordinates `a = 2 y 0 - 1`, `b = 2 y 1 - 1` of a point of the square lie in `[-1,1]` for
`y` in the unit square. -/
lemma abs_two_mul_sub_one_le_one {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (i : Fin 2) : |2 * y i - 1| ≤ 1 := by
  have h : y i ∈ Set.Icc (0 : ℝ) 1 := hy i
  rw [Set.mem_Icc] at h
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- **The square-to-disk map is smooth on all of `ℝ²`.** -/
theorem sqDisk_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sqDisk := by
  have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => (2 * y 0 - 1 : ℝ)) := by fun_prop
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => (2 * y 1 - 1 : ℝ)) := by fun_prop
  have hw0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => sqWeight (2 * y 0 - 1)) :=
    sqWeight_contDiff.comp h0
  have hw1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => sqWeight (2 * y 1 - 1)) :=
    sqWeight_contDiff.comp h1
  have hre : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => (((2 * y 0 - 1) * sqWeight (2 * y 1 - 1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (h0.mul hw1)
  have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => (((2 * y 1 - 1) * sqWeight (2 * y 0 - 1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (h1.mul hw0)
  exact hre.add (him.mul contDiff_const)

/-- **The square-to-disk map is invariant under the antipodal involution of the square's boundary, in
the strong form `sqDisk (seamInv2 y) = - sqDisk y` valid everywhere.** -/
theorem sqDisk_seamInv (y : EuclideanSpace ℝ (Fin 2)) : sqDisk (seamInv2 y) = - sqDisk y := by
  have h0 : (seamInv2 y) 0 = 1 - y 0 := seamInv2_apply_zero y
  have h1 : (seamInv2 y) 1 = 1 - y 1 := seamInv2_apply_one y
  have e0 : sqWeight (2 * (1 - y 0) - 1) = sqWeight (2 * y 0 - 1) := by
    rw [show 2 * (1 - y 0) - 1 = -(2 * y 0 - 1) by ring, sqWeight_even]
  have e1 : sqWeight (2 * (1 - y 1) - 1) = sqWeight (2 * y 1 - 1) := by
    rw [show 2 * (1 - y 1) - 1 = -(2 * y 1 - 1) by ring, sqWeight_even]
  apply Complex.ext
  · rw [Complex.neg_re, sqDisk_apply_re, sqDisk_apply_re, h0, h1]
    simp only [e0, e1]
    ring
  · rw [Complex.neg_im, sqDisk_apply_im, sqDisk_apply_im, h0, h1]
    simp only [e0, e1]
    ring

/-- **The squared modulus of the square-to-disk map on the square.**  Writing `a = 2 y 0 - 1`,
`b = 2 y 1 - 1`, one has `‖sqDisk y‖² = a² + b² - a²b² = 1 - (1-a²)(1-b²)`. -/
theorem norm_sqDisk_sq (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ Submission.Drive.unitBox 1) :
    ‖sqDisk y‖ ^ 2 = 1 - (1 - (2 * y 0 - 1) ^ 2) * (1 - (2 * y 1 - 1) ^ 2) := by
  have h0 := abs_two_mul_sub_one_le_one hy 0
  have h1 := abs_two_mul_sub_one_le_one hy 1
  have hsq : ‖sqDisk y‖ ^ 2
      = ((2 * y 0 - 1) * sqWeight (2 * y 1 - 1)) ^ 2
        + ((2 * y 1 - 1) * sqWeight (2 * y 0 - 1)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sqDisk_apply_re, sqDisk_apply_im]
    ring
  rw [hsq, mul_pow, mul_pow, sqWeight_sq h1, sqWeight_sq h0]
  ring

/-- **The square-to-disk map lands in the closed unit disk on the square.** -/
theorem norm_sqDisk_le_one (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ Submission.Drive.unitBox 1) :
    ‖sqDisk y‖ ≤ 1 := by
  have h0 := abs_two_mul_sub_one_le_one hy 0
  have h1 := abs_two_mul_sub_one_le_one hy 1
  have hsq := norm_sqDisk_sq y hy
  have hle : ‖sqDisk y‖ ^ 2 ≤ 1 := by
    rw [hsq]
    have ha : (2 * y 0 - 1) ^ 2 ≤ 1 := by nlinarith [abs_le.mp h0]
    have hb : (2 * y 1 - 1) ^ 2 ≤ 1 := by nlinarith [abs_le.mp h1]
    nlinarith [sq_nonneg (2 * y 0 - 1), sq_nonneg (2 * y 1 - 1)]
  nlinarith [norm_nonneg (sqDisk y)]

/-- **The square-to-disk map hits the unit circle exactly on the boundary of the square.** -/
theorem norm_sqDisk_eq_one_iff (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ Submission.Drive.unitBox 1) : ‖sqDisk y‖ = 1 ↔ onSeam2 y := by
  have h0 := abs_two_mul_sub_one_le_one hy 0
  have h1 := abs_two_mul_sub_one_le_one hy 1
  have hsq := norm_sqDisk_sq y hy
  have ha1 : (2 * y 0 - 1) ^ 2 ≤ 1 := by nlinarith [abs_le.mp h0]
  have hb1 : (2 * y 1 - 1) ^ 2 ≤ 1 := by nlinarith [abs_le.mp h1]
  have hzero : (1 - (2 * y 0 - 1) ^ 2) * (1 - (2 * y 1 - 1) ^ 2) = 0 ↔ onSeam2 y := by
    rw [mul_eq_zero]
    constructor
    · rintro (h | h)
      · have h2 : (2 * y 0 - 1) ^ 2 = 1 := by linarith
        rcases sq_eq_one_iff.mp h2 with h' | h'
        · exact Or.inr (Or.inl (by linarith))
        · exact Or.inl (by linarith)
      · have h2 : (2 * y 1 - 1) ^ 2 = 1 := by linarith
        rcases sq_eq_one_iff.mp h2 with h' | h'
        · exact Or.inr (Or.inr (Or.inr (by linarith)))
        · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · rintro (h | h | h | h)
      · left; rw [h]; ring
      · left; rw [h]; ring
      · right; rw [h]; ring
      · right; rw [h]; ring
  constructor
  · intro heq
    refine hzero.mp ?_
    have : ‖sqDisk y‖ ^ 2 = 1 := by rw [heq]; norm_num
    linarith [hsq]
  · intro hseam
    have hz : ‖sqDisk y‖ ^ 2 = 1 := by
      rw [hsq, hzero.mpr hseam]
      ring
    nlinarith [norm_nonneg (sqDisk y)]

end

end Work.Drive
