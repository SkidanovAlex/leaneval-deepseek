import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Vanishing of `∫ t, D²ω(x + t • y)[ζ, y]` for `ω` compactly supported and `C²`

For a `C²` function `ω : ℝᵈ → ℝ` with compact support, the integral along any line
`t ↦ x + t • y` of the second iterated derivative evaluated on the pair `(ζ, y)` vanishes.

This is the fundamental-theorem-of-calculus observation that the second derivative of `ω`
in the directions `(ζ, y)` is the derivative of the function `t ↦ Dω(x + t • y)·ζ`
(using the symmetry of the second derivative to exchange the two directions), which is a
`C¹` function with compact support, whose integral of derivative over `ℝ` is zero.
-/

open MeasureTheory
open scoped Topology

noncomputable section

set_option autoImplicit false

namespace Commons.MeasureTheory.Integral

/-- Composing a compactly supported function on `ℝᵈ` with an affine line `t ↦ x + t • y` with
`y ≠ 0` gives a compactly supported function on `ℝ`. -/
private lemma hasCompactSupport_comp_line {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : HasCompactSupport F) {x y : EuclideanSpace ℝ (Fin d)} (hy : y ≠ 0) :
    HasCompactSupport (fun t : ℝ => F (x + t • y)) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin d))).mp
    hF.isBounded
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ) ((r + ‖x‖) / ‖y‖ + 1))
    (isCompact_closedBall 0 _) ?_
  intro t ht
  have hnorm_y : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have ht' : (r + ‖x‖) / ‖y‖ + 1 < dist t (0 : ℝ) := not_le.mp ht
  have ht'' : ((r + ‖x‖) / ‖y‖) < |t| := by
    have : dist t (0 : ℝ) = |t| := by rw [Real.dist_eq, sub_zero]
    rw [this] at ht'; linarith
  have hmul : r + ‖x‖ < |t| * ‖y‖ := by
    have h2 : ((r + ‖x‖) / ‖y‖) * ‖y‖ < |t| * ‖y‖ :=
      mul_lt_mul_of_pos_right ht'' hnorm_y
    rwa [div_mul_cancel₀ _ (ne_of_gt hnorm_y)] at h2
  have hsub : (x + t • y) - x = t • y := by abel
  have h1 : ‖t • y‖ - ‖x‖ ≤ ‖x + t • y‖ := by
    have := norm_sub_le (x + t • y) x
    rw [hsub] at this
    linarith
  rw [norm_smul, Real.norm_eq_abs] at h1
  have hbig : r < ‖x + t • y‖ := by linarith
  exact image_eq_zero_of_notMem_tsupport fun hmem => by
    have hle : dist (x + t • y) 0 ≤ r := Metric.mem_closedBall.mp (hr hmem)
    rw [dist_eq_norm, sub_zero] at hle
    linarith

/-- A continuous compactly supported function on `ℝᵈ`, composed with an affine line
`t ↦ x + t • y` with `y ≠ 0`, is integrable on `ℝ`. -/
private lemma integrable_comp_line {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : HasCompactSupport F) (hFc : Continuous F)
    {x y : EuclideanSpace ℝ (Fin d)} (hy : y ≠ 0) :
    Integrable (fun t : ℝ => F (x + t • y)) :=
  (hFc.comp (by fun_prop)).integrable_of_hasCompactSupport (hasCompactSupport_comp_line hF hy)

/-- Continuity of `p ↦ D²ω(p)[ζ, y]` for a `C²` function `ω`. -/
private lemma continuous_iteratedFDeriv_two_apply {d : ℕ} {ω : EuclideanSpace ℝ (Fin d) → ℝ}
    (hω : ContDiff ℝ 2 ω) (ζ y : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun p : EuclideanSpace ℝ (Fin d) => (iteratedFDeriv ℝ 2 ω p) ![ζ, y]) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin d)) ℝ ![ζ, y]).continuous.comp
    (hω.continuous_iteratedFDeriv (m := 2) (by norm_num))

/-- Continuity of `p ↦ Dω(p)·ζ` for a `C²` function `ω`. -/
private lemma continuous_fderiv_apply {d : ℕ} {ω : EuclideanSpace ℝ (Fin d) → ℝ}
    (hω : ContDiff ℝ 2 ω) (ζ : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun p : EuclideanSpace ℝ (Fin d) => (fderiv ℝ ω p) ζ) :=
  (ContinuousLinearMap.apply ℝ ℝ ζ).continuous.comp (hω.continuous_fderiv (by norm_num))

/-- Compact support of `p ↦ D²ω(p)[ζ, y]` for a compactly supported `C²` function `ω`. -/
private lemma hasCompactSupport_iteratedFDeriv_two_apply {d : ℕ}
    {ω : EuclideanSpace ℝ (Fin d) → ℝ} (hc : HasCompactSupport ω)
    (ζ y : EuclideanSpace ℝ (Fin d)) :
    HasCompactSupport (fun p : EuclideanSpace ℝ (Fin d) => (iteratedFDeriv ℝ 2 ω p) ![ζ, y]) :=
  (hc.iteratedFDeriv 2).comp_left
    (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin d)) ℝ =>
      L ![ζ, y]) (by simp)

/-- Chain rule along the line `s ↦ x + s • y`, together with the symmetry of the second
derivative: the derivative of `s ↦ Dω(x + s • y)·ζ` at `t` is `D²ω(x + t • y)[ζ, y]`. -/
private lemma hasDerivAt_line {d : ℕ} {ω : EuclideanSpace ℝ (Fin d) → ℝ}
    (hω : ContDiff ℝ 2 ω) (x y ζ : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (fderiv ℝ ω (x + s • y)) ζ)
      ((iteratedFDeriv ℝ 2 ω (x + t • y)) ![ζ, y]) t := by
  have hA : HasDerivAt (fun s : ℝ => x + s • y) y t := by
    have h1 := (hasDerivAt_id t).smul_const y |>.const_add x
    simpa using h1
  have hΦ : HasFDerivAt (fderiv ℝ ω) (fderiv ℝ (fderiv ℝ ω) (x + t • y)) (x + t • y) :=
    (((hω.contDiffAt).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero).hasFDerivAt
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ ω (x + s • y))
      ((fderiv ℝ (fderiv ℝ ω) (x + t • y)) y) t :=
    hΦ.comp_hasDerivAt t hA
  have h2 : HasDerivAt (fun s : ℝ => (fderiv ℝ ω (x + s • y)) ζ)
      (((fderiv ℝ (fderiv ℝ ω) (x + t • y)) y) ζ) t :=
    (ContinuousLinearMap.apply ℝ ℝ ζ).hasFDerivAt.comp_hasDerivAt t h1
  have hval : (((fderiv ℝ (fderiv ℝ ω) (x + t • y)) y) ζ)
      = (iteratedFDeriv ℝ 2 ω (x + t • y)) ![ζ, y] := by
    rw [iteratedFDeriv_two_apply]
    exact (hω.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq y ζ
  rw [← hval]
  exact h2

theorem integral_iteratedFDeriv_two_apply_eq_zero {d : ℕ} {ω : EuclideanSpace ℝ (Fin d) → ℝ}
    (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω) (x y ζ : EuclideanSpace ℝ (Fin d)) :
    ∫ t : ℝ, (iteratedFDeriv ℝ 2 ω (x + t • y)) ![ζ, y] = 0 := by
  by_cases hy : y = 0
  · rw [hy]
    simp [iteratedFDeriv_two_apply]
  · refine MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun t : ℝ => (fderiv ℝ ω (x + t • y)) ζ)
      (f' := fun t : ℝ => (iteratedFDeriv ℝ 2 ω (x + t • y)) ![ζ, y]) ?_ ?_ ?_
    · intro t
      exact hasDerivAt_line hω x y ζ t
    · exact integrable_comp_line (hasCompactSupport_iteratedFDeriv_two_apply hc ζ y)
        (continuous_iteratedFDeriv_two_apply hω ζ y) hy
    · exact integrable_comp_line (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc ζ)
        (continuous_fderiv_apply hω ζ) hy

end Commons.MeasureTheory.Integral