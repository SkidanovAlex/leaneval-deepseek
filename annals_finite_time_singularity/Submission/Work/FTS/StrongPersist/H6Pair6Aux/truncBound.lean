import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval

open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-! ## The radial weight `w` and the auxiliary function `t ↦ t (w t)²`

Everything is completely elementary: `(w t)² = (1+t)⁴/t⁴`, so `t (w t)² = (1+t)⁴/t³`, whose
derivative is `(1+t)³ (t-3)/t⁴`, and `|t - 3| ≤ 4 (1+t)` on `(0,∞)` gives the pointwise bound
`|deriv| ≤ 4 (w t)²` used in `truncBound`. -/

/-- `(w t)² = (1+t)⁴/t⁴` for the radial weight `w t = (1+t)²/t²` (the identity also holds at
`t = 0`, since both sides vanish by totality of division). -/
lemma w_sq_eq (t : ℝ) : (Work.Spaces.w t) ^ 2 = (1 + t) ^ 4 / t ^ 4 := by
  rw [Work.Spaces.w, div_pow, ← pow_mul, ← pow_mul]

/-- The derivative of `t ↦ t (w t)²` on `(0,∞)`: `t (w t)² = (1+t)⁴/t³`. -/
lemma deriv_tmul_w_sq {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun s : ℝ => s * (Work.Spaces.w s) ^ 2)
      (((1 + z) ^ 3 * (z - 3)) / z ^ 4) z := by
  have hcongr : (fun s : ℝ => s * (Work.Spaces.w s) ^ 2)
      =ᶠ[𝓝 z] (fun s : ℝ => (1 + s) ^ 4 / s ^ 3) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with s _hs
    have hs4 : (Work.Spaces.w s) ^ 2 = (1 + s) ^ 4 / s ^ 4 := w_sq_eq s
    rw [hs4]
    field_simp
  have h1 : HasDerivAt (fun s : ℝ => (1 + s) ^ 4) (4 * (1 + z) ^ 3) z := by
    have h : HasDerivAt (fun s : ℝ => 1 + s) (1 : ℝ) z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have h3 := h.pow 4
    norm_num at h3
    exact h3
  have h2 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * z ^ 2) z := by
    have h3 := (hasDerivAt_id z).pow 3
    norm_num at h3
    exact h3
  have h3 := h1.div h2 (pow_ne_zero 3 (ne_of_gt hz))
  have hv : (4 * (1 + z) ^ 3 * z ^ 3 - (1 + z) ^ 4 * (3 * z ^ 2)) / (z ^ 3) ^ 2
      = ((1 + z) ^ 3 * (z - 3)) / z ^ 4 := by
    field_simp
    ring
  rw [← hv]
  exact h3.congr_of_eventuallyEq hcongr

/-- The pointwise bound on the derivative of `t ↦ t (w t)²` on `(0,∞)`:
`|(1+t)³ (t-3)/t⁴| ≤ 4 (w t)²`, because `|t-3| ≤ 4(1+t)`. -/
lemma abs_deriv_tmul_w_sq_le {z : ℝ} (hz : 0 < z) :
    |((1 + z) ^ 3 * (z - 3)) / z ^ 4| ≤ 4 * (Work.Spaces.w z) ^ 2 := by
  rw [w_sq_eq]
  have hz4 : (0 : ℝ) < z ^ 4 := pow_pos hz 4
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hb : |z - 3| ≤ 4 * (1 + z) := by
    rw [abs_le]; constructor <;> linarith
  have hstep : |((1 + z) ^ 3 * (z - 3)) / z ^ 4| = (1 + z) ^ 3 * |z - 3| / z ^ 4 := by
    rw [abs_div, abs_mul, abs_pow, abs_of_pos h1z, abs_of_pos hz4]
  rw [hstep]
  calc (1 + z) ^ 3 * |z - 3| / z ^ 4
      ≤ (1 + z) ^ 3 * (4 * (1 + z)) / z ^ 4 := by
        apply div_le_div_of_nonneg_right _ hz4.le
        exact mul_le_mul_of_nonneg_left hb (pow_nonneg h1z.le 3)
    _ = 4 * ((1 + z) ^ 4 / z ^ 4) := by
        field_simp

/-- Truncated form of the radial self-pairing bound.  With
`H t = (w t)^2 * (Y t)^2`, `G t = ((w t)^2 * (Y t)^2) * t` and
`F z = (w z)^2 * ((z * deriv Y z) * Y z)`, one has on `(0,∞)`
`deriv (fun t => t * (w t)^2) t = (1+t)^3 * (t-3) / t^4` (from `(w t)^2 = (1+t)^4/t^4`),
so that `deriv G t = deriv (fun s => s * (w s)^2) t * (Y t)^2 + 2 * F t`, and
`|deriv (fun t => t * (w t)^2) t| ≤ 4 * (w t)^2` for `t > 0` (as `|t-3| ≤ 4*(1+t)`).
Integrating the derivative identity over `[a,b] ⊂ (0,∞)` (FTC) then gives the bound below.
Requires `open scoped Interval` for the `a..b` notation. -/
theorem truncBound {Y : ℝ → ℝ} (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0)) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    |∫ z in a..b, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)|
      ≤ (1 / 2) * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b
            + ((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a)
        + 2 * ∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
  have huI : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  have hYd : ∀ z ∈ Set.Icc a b, HasDerivAt Y (deriv Y z) z := fun z hz =>
    ((hY.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (hsub hz))).hasDerivAt
  have hYc : ContinuousOn Y (Set.Icc a b) := (hY.continuousOn).mono hsub
  have hYdc : ContinuousOn (deriv Y) (Set.Icc a b) :=
    (hY.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc a b) := by
    change ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc a b)
    refine ContinuousOn.div ?_ ?_ (fun z hz => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hz.1)))
    · fun_prop
    · fun_prop
  have hW'c : ContinuousOn (fun z : ℝ => ((1 + z) ^ 3 * (z - 3)) / z ^ 4) (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ (fun z hz => pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le ha hz.1)))
    · fun_prop
    · fun_prop
  have hInt : ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) → IntervalIntegrable f volume a b :=
    fun f hf => (show ContinuousOn f (Set.uIcc a b) from by rw [huI]; exact hf).intervalIntegrable
  have habsW' : ∀ z ∈ Set.Icc a b,
      |((1 + z) ^ 3 * (z - 3)) / z ^ 4| ≤ 4 * (Work.Spaces.w z) ^ 2 :=
    fun z hz => abs_deriv_tmul_w_sq_le (hsub hz)
  have hWd : ∀ z ∈ Set.Icc a b, HasDerivAt (fun s : ℝ => s * (Work.Spaces.w s) ^ 2)
      (((1 + z) ^ 3 * (z - 3)) / z ^ 4) z := fun z hz => deriv_tmul_w_sq (hsub hz)
  -- the derivative of `t ↦ t (w t)² (Y t)²`
  have hGd : ∀ z ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => t * (Work.Spaces.w t) ^ 2 * (Y t) ^ 2)
        (((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2
          + 2 * ((Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))) z := by
    intro z hz
    rw [huI] at hz
    have h1 := hWd z hz
    have h2 := (hYd z hz).pow 2
    have h3 := h1.mul h2
    have hfun : (fun t : ℝ => t * (Work.Spaces.w t) ^ 2 * (Y t) ^ 2)
        = (fun s : ℝ => s * (Work.Spaces.w s) ^ 2) * (fun s : ℝ => (Y s) ^ 2) := by
      funext s; rfl
    rw [hfun]
    convert h3 using 1
    simp only [Pi.pow_apply]
    ring
  have hIntI1 : IntervalIntegrable
      (fun z : ℝ => ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2) volume a b :=
    hInt _ (hW'c.mul (hYc.pow 2))
  have hIntI2 : IntervalIntegrable
      (fun z : ℝ => 2 * ((Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))) volume a b :=
    hInt _ (continuousOn_const.mul ((hw.pow 2).mul ((continuousOn_id.mul hYdc).mul hYc)))
  have hIntG' : IntervalIntegrable
      (fun z : ℝ => ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2
        + 2 * ((Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))) volume a b :=
    hInt _ ((hW'c.mul (hYc.pow 2)).add (continuousOn_const.mul
      ((hw.pow 2).mul ((continuousOn_id.mul hYdc).mul hYc))))
  -- FTC for `t ↦ t (w t)² (Y t)²`
  have hFTC : ∫ z in a..b, (((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2
        + 2 * ((Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)))
      = b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
        - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro z hz; exact hGd z hz
    · exact hIntG'
  have hsplit : (∫ z in a..b, (((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2
        + 2 * ((Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))))
      = (∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2)
        + 2 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)) := by
    rw [intervalIntegral.integral_add hIntI1 hIntI2, intervalIntegral.integral_const_mul]
  -- bound on the `(w')`-half
  have hI1 : |∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2|
      ≤ 4 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
    calc |∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2|
        ≤ ∫ z in a..b, |((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ = ∫ z in a..b, |((1 + z) ^ 3 * (z - 3)) / z ^ 4| * (Y z) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro z _
          dsimp only
          rw [abs_mul, abs_of_nonneg (sq_nonneg (Y z))]
      _ ≤ ∫ z in a..b, 4 * ((Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
          apply intervalIntegral.integral_mono_on hab
          · exact hInt _ ((hW'c.abs).mul (hYc.pow 2))
          · exact hInt _ (continuousOn_const.mul ((hw.pow 2).mul (hYc.pow 2)))
          · intro z hz
            calc |((1 + z) ^ 3 * (z - 3)) / z ^ 4| * (Y z) ^ 2
                ≤ (4 * (Work.Spaces.w z) ^ 2) * (Y z) ^ 2 :=
                  mul_le_mul_of_nonneg_right (habsW' z hz) (sq_nonneg (Y z))
              _ = 4 * ((Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by ring
      _ = 4 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
  -- the integration-by-parts identity for `∫ w² (z Y') Y`
  have hkey : 2 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))
      = (b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
        - ∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2 := by
    linarith [hFTC, hsplit]
  have hI2 : (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))
      = (1 / 2) * ((b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
        - (∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2)) := by
    linarith [hkey]
  rw [hI2]
  have hB1 : (0 : ℝ) ≤ b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2 :=
    mul_nonneg (mul_nonneg (le_trans ha.le hab) (sq_nonneg _)) (sq_nonneg _)
  have hB2 : (0 : ℝ) ≤ a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2 :=
    mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) (sq_nonneg _)
  have hB : |b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2 - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2|
      ≤ b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2 + a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2 := by
    have := abs_sub_le (b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2) 0
      (a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
    simpa [abs_of_nonneg hB1, abs_of_nonneg hB2] using this
  calc |(1 / 2) * ((b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
        - (∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2))|
      = (1 / 2) * |(b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
        - (∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2)| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ (1 / 2) * (|b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2|
        + |∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2|) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa using abs_sub_le (b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
            - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2) 0
            (∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2)
    _ ≤ (1 / 2) * ((b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          + a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
        + 4 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith [hB, hI1]
    _ = (1 / 2) * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b
          + ((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a)
        + 2 * ∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by ring

end Work.FTS.StrongPersist.H6Pair6Aux
