import Mathlib
import Submission.Work.Drive.chordSweepDefs

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- The norm of a combination of two orthonormal vectors: for `‖f1‖ = ‖f2‖ = 1`
and `inner ℝ f1 f2 = 0` one has `‖a • f1 + b • f2‖ ^ 2 = a ^ 2 + b ^ 2`
(Pythagoras in the plane spanned by `f1`, `f2`). -/
lemma orthonormal_norm_sq {f1 f2 : Space} (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1)
    (hperp : inner ℝ f1 f2 = 0) (a b : ℝ) :
    ‖a • f1 + b • f2‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real]
  have hxy : inner ℝ (a • f1) (b • f2) = 0 := by
    simp [inner_smul_left, inner_smul_right, hperp]
  have ha : ‖a • f1‖ ^ 2 = a ^ 2 := by
    rw [norm_smul, h1, mul_one, Real.norm_eq_abs, sq_abs]
  have hb : ‖b • f2‖ ^ 2 = b ^ 2 := by
    rw [norm_smul, h2, mul_one, Real.norm_eq_abs, sq_abs]
  rw [ha, hb, hxy]
  ring

/-- A circle of radius `R > 0` in the plane spanned by the orthonormal pair
`f1, f2`, centred at `c`, with `t ↦ cos t • f1 + sin t • f2` as its polar
parametrization, is a smooth knot. -/
theorem polarCircle_isSmoothKnot {c f1 f2 : LeanEval.KnotTheory.Quadrisecant.Space} {R : ℝ}
    (hR : 0 < R) (h1 : ‖f1‖ = 1) (h2 : ‖f2‖ = 1) (hperp : inner ℝ f1 f2 = 0) :
    LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot
      (fun t : ℝ => c + R • (Real.cos t • f1 + Real.sin t • f2)) := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- analyticity: `cos` and `sin` are `C^ω`, scalar multiplication and
    -- translation preserve `C^ω`
    fun_prop
  · -- periodicity with period `2π`
    intro t
    simp only [period, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · -- injectivity on `[0, period)`
    intro t ht s hs h
    -- equal images give equal points of the plane spanned by `f1, f2`
    have hXY : Real.cos t • f1 + Real.sin t • f2 = Real.cos s • f1 + Real.sin s • f2 := by
      have h2' : R • (Real.cos t • f1 + Real.sin t • f2)
          = R • (Real.cos s • f1 + Real.sin s • f2) := add_left_cancel h
      have h3 := congrArg (fun z : Space => R⁻¹ • z) h2'
      simpa [inv_smul_smul₀ hR0] using h3
    have hperp' : inner ℝ f2 f1 = 0 := by rw [real_inner_comm, hperp]
    -- pairing with the orthonormal frame recovers the two coordinates
    have hcos : Real.cos t = Real.cos s := by
      have hh := congrArg (fun z : Space => inner ℝ f1 z) hXY
      simpa [inner_add_right, inner_smul_right, h1, hperp] using hh
    have hsin : Real.sin t = Real.sin s := by
      have hh := congrArg (fun z : Space => inner ℝ f2 z) hXY
      simpa [inner_add_right, inner_smul_right, h2, hperp'] using hh
    have hcos1 : Real.cos (t - s) = 1 := by
      rw [Real.cos_sub, ← hcos, ← hsin]
      nlinarith [Real.sin_sq_add_cos_sq t]
    have ht2 : t < 2 * Real.pi := by simpa [period] using ht.2
    have hs2 : s < 2 * Real.pi := by simpa [period] using hs.2
    have hb1 : -(2 * Real.pi) < t - s := by nlinarith [ht.1, hs2]
    have hb2 : t - s < 2 * Real.pi := by nlinarith [ht2, hs.1]
    have hts0 : t - s = 0 := (Real.cos_eq_one_iff_of_lt_of_lt hb1 hb2).mp hcos1
    linarith
  · -- regularity: the velocity has norm `R > 0`
    intro t
    have hderiv : HasDerivAt (fun x : ℝ => c + R • (Real.cos x • f1 + Real.sin x • f2))
        (R • ((-Real.sin t) • f1 + Real.cos t • f2)) t := by
      have hc : HasDerivAt (fun x : ℝ => Real.cos x • f1) ((-Real.sin t) • f1) t :=
        (Real.hasDerivAt_cos t).smul_const f1
      have hs : HasDerivAt (fun x : ℝ => Real.sin x • f2) ((Real.cos t) • f2) t :=
        (Real.hasDerivAt_sin t).smul_const f2
      exact ((hc.add hs).const_smul R).const_add c
    have hvel : velocity (fun x : ℝ => c + R • (Real.cos x • f1 + Real.sin x • f2)) t
        = R • ((-Real.sin t) • f1 + Real.cos t • f2) := by
      unfold velocity
      exact hderiv.deriv
    rw [hvel]
    intro hzero
    have hv : ‖(-Real.sin t) • f1 + Real.cos t • f2‖ = 1 := by
      have hh := orthonormal_norm_sq h1 h2 hperp (-Real.sin t) (Real.cos t)
      rw [neg_sq, Real.sin_sq_add_cos_sq] at hh
      nlinarith [norm_nonneg ((-Real.sin t) • f1 + Real.cos t • f2), hh]
    have hnorm : ‖R • ((-Real.sin t) • f1 + Real.cos t • f2)‖ = 0 := by
      rw [hzero, norm_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, hv, mul_one] at hnorm
    exact hR0 hnorm

end Work.Drive
