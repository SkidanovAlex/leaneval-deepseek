import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# The horospherical coordinates of `hptOf ξ y D`

`hptOf ξ y D = ((1 + D²‖y‖²)/(2D) − D/2) • ξ + D • y` is the point of `ℍⁿ` which sits on the
horosphere of `ξ` of level `D` and has flat coordinate `y ∈ ξ^⊥`.

The three defining properties of that point are recorded here: its Busemann level is `D`, its
normalised flat coordinate is `y`, and its Busemann function equals `log D`.

Everything is a computation in the chart: with `a = (1 + D²‖y‖²)/(2D) − D/2` and `ξ ⊥ y`,
`⟪hptOf, ξ⟫ = a` and `‖hptOf‖² = a² + D²‖y‖²`, whence `tpart (hptOf) = a + D`
(because `(a+D)² = 1 + a² + D²‖y‖²` and `a + D > 0`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- `⟪hptOf ξ y D, ξ⟫` is the scalar multiplying `ξ` in `hptOf ξ y D`, since `ξ ⊥ y`. -/
lemma hptOf_inner_xi {ξ : E n} (hξ : ξ ∈ Sph n) {y : E n} (hy : inner ℝ y ξ = 0) (D : ℝ) :
    inner ℝ (hptOf ξ y D) ξ = (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 := by
  have hξnorm : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hξ1 : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hξnorm]; norm_num
  simp only [hptOf, inner_add_left, real_inner_smul_left, hξ1, hy, mul_zero, mul_one]
  ring

/-- `‖hptOf ξ y D‖² = a² + D²‖y‖²` with `a` the scalar multiplying `ξ`: the two summands of
`hptOf ξ y D` are orthogonal. -/
lemma hptOf_norm_sq {ξ : E n} (hξ : ξ ∈ Sph n) {y : E n} (hy : inner ℝ y ξ = 0) (D : ℝ) :
    ‖hptOf ξ y D‖ ^ 2 =
      ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2) ^ 2 + D ^ 2 * ‖y‖ ^ 2 := by
  have hξnorm : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hξ1 : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hξnorm]; norm_num
  have hyξ : inner ℝ ξ y = 0 := by rw [real_inner_comm]; exact hy
  rw [← real_inner_self_eq_norm_sq]
  simp only [hptOf, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hξ1, hy, hyξ, real_inner_self_eq_norm_sq, mul_zero, mul_one]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hξnorm, mul_one]
  ring

/-- the time coordinate of `hptOf ξ y D` is the sum of the `ξ`-scalar and `D`. -/
lemma hptOf_tpart_eq {ξ : E n} (hξ : ξ ∈ Sph n) {y : E n} (hy : inner ℝ y ξ = 0)
    {D : ℝ} (hD : 0 < D) :
    tpart (hptOf ξ y D) = (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 + D := by
  have hnorm := hptOf_norm_sq hξ hy D
  have hkey : 1 + ‖hptOf ξ y D‖ ^ 2 = ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 + D) ^ 2 := by
    rw [hnorm]; field_simp; ring
  have hpos : 0 ≤ (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 + D := by
    have : (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 + D = (1 + D ^ 2 * ‖y‖ ^ 2 + D ^ 2) / (2 * D) := by
      field_simp; ring
    rw [this]; positivity
  rw [tpart, hkey, Real.sqrt_sq hpos]

theorem hptOfLevelYc {n : ℕ} (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    {y : Submission.Mostow.E n} (hy : inner ℝ y ξ = 0) {D : ℝ} (hD : 0 < D) :
    Work.Mostow.lev ξ (Work.Mostow.hptOf ξ y D) = D ∧
      Work.Mostow.yc ξ (Work.Mostow.hptOf ξ y D) = y ∧
      Submission.Mostow.busemann ξ (Work.Mostow.hptOf ξ y D) = Real.log D := by
  have hinner := hptOf_inner_xi hξ hy D
  have htpart := hptOf_tpart_eq hξ hy hD
  have hlev : lev ξ (hptOf ξ y D) = D := by
    rw [lev, htpart, hinner]; ring
  have hbus : busemann ξ (hptOf ξ y D) = Real.log D := by
    rw [busemann, htpart, hinner]; norm_num
  have hwc : wc ξ (hptOf ξ y D) = D • y := by
    rw [wc, hinner]
    simp only [hptOf]
    abel
  have hyc : yc ξ (hptOf ξ y D) = y := by
    rw [yc, hlev, hwc, inv_smul_smul₀ (ne_of_gt hD)]
  exact ⟨hlev, hyc, hbus⟩

end Work.Mostow
