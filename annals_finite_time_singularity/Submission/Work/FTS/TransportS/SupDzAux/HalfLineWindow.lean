/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial Hardy inequality without a decay hypothesis (window form)

`Work.Spaces.HardyZ` bounds a one-dimensional function on the half line by the weighted
`L²`-norm of its radial derivative `D_z h = z h'`,

  `h(z)² ≤ ∫_s (D_z h(s))² w(s)² ds`,   `w(s) = (1+s)²/s²`,

but only under the hypothesis that `h` *decays at infinity*.  In the open class
(`Work.FTS.EllipticEst.SmoothOpen` + `Work.Spaces.HkMem`) no such decay is available: the
`HkMem`-hypothesis only gives, for almost every *angle*, the finiteness of the radial
`s`-integral of the weighted square of the derivative.  The lemma of this file provides the
replacement: a *window* form in which the unknown value at infinity is replaced by an
average over a window `[R₀, 2R₀]`, which is small when `R₀` is large because the whole
`z`-integral of `h²` is finite.

* `half_line_window_bound` is the one-dimensional statement.  For `0 < z₀ ≤ R₀` and a
  function `h` which is `C¹` on `[z₀, 2R₀]`,

    `h(z₀)² ≤ 2 ∫_{z₀}^{2R₀} (z h'(z) w(z))² dz + (2/R₀) ∫_{R₀}^{2R₀} h(z)² dz`.

  Proof: the fundamental theorem of calculus `h(z₀) - h(R) = ∫_{z₀}^R h'` for
  `R ∈ [R₀, 2R₀]`, the Cauchy–Schwarz inequality in the form
  `h' = (z h' w) · ψ` with `ψ(s) = s/(1+s)²`,
  `∫_{z₀}^R ψ² ≤ ∫_0^∞ ψ² ≤ 1`, and the elementary `(a+b)² ≤ 2a² + 2b²` together with the
  average of the constant `(h z₀)²` over the window `[R₀, 2R₀]` of length `R₀`.

All declarations here are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts -/

/-- The weight `w` is positive on `(0,∞)`. -/
theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

/-- `1 ≤ w z` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [sq_nonneg z]

/-- The algebraic identity behind the weighted Cauchy–Schwarz step:
`(z h'(z) w(z)) · (z/(1+z)²) = h'(z)` for `z > 0`. -/
theorem w_mul_psi_eq {h' : ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    (z * h' z * Work.Spaces.w z) * (z / (1 + z) ^ 2) = h' z := by
  have h1 : (1 + z) ≠ 0 := ne_of_gt (by linarith)
  have hz' : z ≠ 0 := ne_of_gt hz
  simp only [Work.Spaces.w]
  field_simp

/-! ## The window form of the radial Hardy inequality -/

/-- **The radial Hardy inequality in window form.**  For `0 < z₀ ≤ R₀`, a function `h` of
class `C¹` on `[z₀, 2R₀]` whose square is integrable on `[R₀, 2R₀]`,

  `h(z₀)² ≤ 2 ∫_{z₀}^{2R₀} (z h'(z) w(z))² dz + (2/R₀) ∫_{R₀}^{2R₀} h(z)² dz`.

The second term is the price of the missing decay hypothesis; it is an average over the
window `[R₀, 2R₀]`, hence tends to `0` for fixed `L²`-data as `R₀ → ∞`. -/
theorem half_line_window_bound {h h' : ℝ → ℝ} {z₀ R₀ : ℝ} (hz₀ : 0 < z₀) (hR : z₀ ≤ R₀)
    (hderiv : ∀ x ∈ Set.Icc z₀ (2 * R₀), HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h (Set.Icc R₀ (2 * R₀)))
    (hcont' : ContinuousOn h' (Set.Icc z₀ (2 * R₀)))
    (hint : IntegrableOn (fun x => (h x) ^ 2) (Set.Icc R₀ (2 * R₀))) :
    (h z₀) ^ 2 ≤ 2 * (∫ x in z₀..(2 * R₀), (x * h' x * Work.Spaces.w x) ^ 2)
      + (2 / R₀) * ∫ x in R₀..(2 * R₀), (h x) ^ 2 := by
  have hR₀ : 0 < R₀ := lt_of_lt_of_le hz₀ hR
  have hz2R : z₀ ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  -- the weighted square of the derivative, as an interval integral over the big window
  set P : ℝ := ∫ x in z₀..(2 * R₀), (x * h' x * Work.Spaces.w x) ^ 2 with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact intervalIntegral.integral_nonneg hz2R fun x _ => sq_nonneg _
  -- the "key" bound `(h z₀ - h R)² ≤ P` for every `R ∈ [R₀, 2R₀]`
  have hkey : ∀ R ∈ Set.Icc R₀ (2 * R₀), (h z₀ - h R) ^ 2 ≤ P := by
    intro R hRmem
    have hzR : z₀ ≤ R := le_trans hR hRmem.1
    have hRle : R ≤ 2 * R₀ := hRmem.2
    have hsub' : Set.Icc z₀ R ⊆ Set.Icc z₀ (2 * R₀) := Set.Icc_subset_Icc le_rfl hRle
    -- the weighted derivative is continuous on the big window `[z₀, 2R₀]`
    have hWc : ContinuousOn (fun x => x * h' x * Work.Spaces.w x) (Set.Icc z₀ (2 * R₀)) := by
      refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz₀ hx.1))
    have hAc : ContinuousOn (fun x => (x * h' x * Work.Spaces.w x) ^ 2)
        (Set.Icc z₀ (2 * R₀)) := hWc.pow 2
    -- the two factors of the Cauchy–Schwarz step are continuous on `[z₀,R]`
    have hcontA : ContinuousOn (fun x => x * h' x * Work.Spaces.w x) (Set.uIcc z₀ R) := by
      rw [Set.uIcc_of_le hzR]
      exact hWc.mono hsub'
    have hcontψ : ContinuousOn (fun x => x / (1 + x) ^ 2) (Set.uIcc z₀ R) := by
      rw [Set.uIcc_of_le hzR]
      refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    -- the fundamental theorem of calculus
    have hFTC : ∫ x in z₀..R, h' x = h R - h z₀ := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
      · intro x hx
        rw [Set.uIcc_of_le hzR] at hx
        exact hderiv x ⟨hx.1, le_trans hx.2 hRle⟩
      · refine (show ContinuousOn h' (Set.uIcc z₀ R) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hzR]
        exact hcont'.mono hsub'
    -- the Cauchy–Schwarz inequality for the interval integral
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt z₀ R hzR hcontA hcontψ
    -- the product is the derivative
    have hcongr : ∫ x in z₀..R, (x * h' x * Work.Spaces.w x) * (x / (1 + x) ^ 2)
        = ∫ x in z₀..R, h' x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hzR] at hx
      exact w_mul_psi_eq (lt_of_lt_of_le hz₀ hx.1)
    -- the `ψ`-factor has mass at most one
    have hpsi : ∫ x in z₀..R, (x / (1 + x) ^ 2) ^ 2 ≤ 1 :=
      Work.Spaces.hardyZ_integral_psi_sq_le_one hz₀.le hzR
    -- the first factor is dominated by `P`
    have hAint : IntervalIntegrable (fun x => (x * h' x * Work.Spaces.w x) ^ 2)
        volume z₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x => (x * h' x * Work.Spaces.w x) ^ 2)
        (Set.uIcc z₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      exact hAc
    have hA : ∫ x in z₀..R, (x * h' x * Work.Spaces.w x) ^ 2 ≤ P := by
      rw [hPdef]
      exact intervalIntegral.integral_mono_interval le_rfl hzR hRle
        (Filter.Eventually.of_forall fun x => sq_nonneg _) hAint
    have hsq : (h z₀ - h R) ^ 2 ≤ P := by
      have h1 : (h z₀ - h R) ^ 2
          = (∫ x in z₀..R, (x * h' x * Work.Spaces.w x) * (x / (1 + x) ^ 2)) ^ 2 := by
        rw [hcongr, hFTC]
        ring
      have hAfnn : 0 ≤ ∫ x in z₀..R, (x * h' x * Work.Spaces.w x) ^ 2 :=
        intervalIntegral.integral_nonneg hzR fun x _ => sq_nonneg _
      have hBnn : 0 ≤ ∫ x in z₀..R, (x / (1 + x) ^ 2) ^ 2 :=
        intervalIntegral.integral_nonneg hzR fun x _ => sq_nonneg _
      have h2 : (∫ x in z₀..R, (x * h' x * Work.Spaces.w x) * (x / (1 + x) ^ 2)) ^ 2
          = |∫ x in z₀..R, (x * h' x * Work.Spaces.w x) * (x / (1 + x) ^ 2)| ^ 2 := by
        rw [sq_abs]
      rw [h1, h2]
      have h3 : |∫ x in z₀..R, (x * h' x * Work.Spaces.w x) * (x / (1 + x) ^ 2)| ^ 2
          ≤ (Real.sqrt (∫ x in z₀..R, (x * h' x * Work.Spaces.w x) ^ 2)) ^ 2
            * (Real.sqrt (∫ x in z₀..R, (x / (1 + x) ^ 2) ^ 2)) ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
      rw [Real.sq_sqrt hAfnn, Real.sq_sqrt hBnn] at h3
      nlinarith [h3, hA, hpsi, hAfnn, hPnn]
    exact hsq
  -- average the pointwise bound over the window
  have hpt : ∀ R ∈ Set.Icc R₀ (2 * R₀), (h z₀) ^ 2 ≤ 2 * P + 2 * (h R) ^ 2 := by
    intro R hRmem
    have h1 : (h z₀) ^ 2 ≤ 2 * (h z₀ - h R) ^ 2 + 2 * (h R) ^ 2 :=
      by nlinarith [sq_nonneg (h z₀ - 2 * h R)]
    nlinarith [h1, hkey R hRmem]
  -- interval integrability of the two sides
  have hIntL : IntervalIntegrable (fun _ : ℝ => (h z₀) ^ 2) volume R₀ (2 * R₀) :=
    intervalIntegrable_const
  have hcontR : ContinuousOn (fun x : ℝ => 2 * P + 2 * (h x) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
    continuousOn_const.add ((continuousOn_const.mul (hcont.pow 2)))
  have hIntR : IntervalIntegrable (fun x : ℝ => 2 * P + 2 * (h x) ^ 2) volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => 2 * P + 2 * (h x) ^ 2)
      (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hcontR
  have hmono := intervalIntegral.integral_mono_on hR2R hIntL hIntR (fun x hx => hpt x hx)
  -- compute the two interval integrals
  have hL : ∫ x in R₀..(2 * R₀), (h z₀) ^ 2 = (h z₀) ^ 2 * R₀ := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hIntC : IntervalIntegrable (fun _ : ℝ => 2 * P) volume R₀ (2 * R₀) :=
    intervalIntegrable_const
  have hIntH : IntervalIntegrable (fun x : ℝ => 2 * (h x) ^ 2) volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => 2 * (h x) ^ 2) (Set.uIcc R₀ (2 * R₀)) from ?_)
      |>.intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact (hcont.pow 2).const_mul 2
  have hRint : ∫ x in R₀..(2 * R₀), (2 * P + 2 * (h x) ^ 2)
      = 2 * P * R₀ + 2 * ∫ x in R₀..(2 * R₀), (h x) ^ 2 := by
    rw [intervalIntegral.integral_add hIntC hIntH, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  rw [hL, hRint] at hmono
  -- divide by `R₀`
  have hQnn : 0 ≤ ∫ x in R₀..(2 * R₀), (h x) ^ 2 :=
    intervalIntegral.integral_nonneg hR2R fun x _ => sq_nonneg _
  have hid : 2 * P + (2 / R₀) * (∫ x in R₀..(2 * R₀), (h x) ^ 2)
      = (2 * P * R₀ + 2 * (∫ x in R₀..(2 * R₀), (h x) ^ 2)) / R₀ := by
    field_simp
  rw [hid, le_div_iff₀ hR₀]
  linarith [hmono]

end Work.FTS.TransportS
