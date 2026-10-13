/-
# `Work.FTS.EllSol.EllPkgAux.mollSliceBound`

The dominating function

  `MGf G w = 1 + |G w (π/4)| + |∂_θG w (π/4)| + √(E2s G w)`

of the angular slice of a trace-class datum `G` dominates `|G w θ|` for every `θ ∈ (0, π/2)`,
and it is locally integrable in `w` on `(0, ∞)`.

The pointwise bound is the second-order Taylor expansion of the slice about `θ₀ = π/4`
together with the `σ`-weighted Cauchy–Schwarz inequality
`∫|f''| ≤ √(π/2) √(∫ (f'')²σ)`, where `σ = thEta θ = sin(2θ)^{-η}` and `η = 99/100`
(the latter is `Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted`).

The local integrability of `MGf` follows from the continuity in `w` of the two interior slice
values `G w (π/4)`, `∂_θG w (π/4)` and from the domination
`√(E2s G w) ≤ 1 + ttIntS G w`, the honest `H^0`-mass of `∂_θ²G` (which is integrable in `w`
by the `FourInts` hypothesis).  Measurability in `w` of the slice energy is
`Work.FTS.EllSol.EllPkgAux.MollAux.aesmE2s`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollAux.aesmE2s
import Submission.Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul
import Submission.Work.FTS.EllSol.Base
import Submission.Work.FTS.EllSol.c2_deriv_sub_eq_intervalIntegral
import Submission.Work.FTS.EllSol.ASlotRoute.Auxiliary.taylorSecondOrderIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-! ## Elementary one-dimensional and angular facts -/

/-- `√a ≤ 1 + a` for `a ≥ 0`. -/
theorem sqrt_le_one_add_self {a : ℝ} (ha : 0 ≤ a) : Real.sqrt a ≤ 1 + a := by
  have h : a ≤ (1 + a) ^ 2 := by nlinarith
  calc Real.sqrt a ≤ Real.sqrt ((1 + a) ^ 2) := Real.sqrt_le_sqrt h
    _ = 1 + a := Real.sqrt_sq (by linarith)

/-- The radial weight is at least `1`. -/
theorem one_le_w {w : ℝ} (hw : 0 < w) : 1 ≤ Work.Spaces.w w := by
  rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < w ^ 2)]
  nlinarith

/-- The squared radial weight is at least `1`. -/
theorem one_le_w_sq {w : ℝ} (hw : 0 < w) : 1 ≤ (Work.Spaces.w w) ^ 2 := by
  calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (Work.Spaces.w w) ^ 2 := pow_le_pow_left₀ (by norm_num) (one_le_w hw) 2

/-- The radial weight is positive for `w > 0`. -/
theorem w_pos {w : ℝ} (hw : 0 < w) : 0 < Work.Spaces.w w := by
  rw [Work.Spaces.w]
  exact div_pos (by positivity) (by positivity)

/-- The angular weight is nonnegative on `Iθ`. -/
theorem thEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

/-- On the open angular interval the weight is at least `1`. -/
theorem one_le_thEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hneg : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos hs0 hs1 hneg
  rw [Real.one_rpow] at h
  simpa [Work.FTS.EllipticEst.thEta] using h

/-- Almost every point of `Iθ` is an interior point. -/
theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The angular weight is at least `1` almost everywhere on `Iθ`. -/
theorem one_le_thEta_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact one_le_thEta_of_mem_Ioo hθ

/-! ## The slice energy and the honest `H^0`-mass -/

/-- The angular slice energy is nonnegative. -/
theorem e2s_nonneg (G : ℝ → ℝ → ℝ) (w : ℝ) : 0 ≤ E2s G w := by
  rw [E2s]
  refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
  intro θ hθ
  exact mul_nonneg (sq_nonneg _) (thEta_nonneg_of_mem_Iθ hθ)

/-- `ttIntS` is the squared radial weight times the slice energy. -/
theorem ttIntS_eq (G : ℝ → ℝ → ℝ) (w : ℝ) :
    Work.EllipticEst.Core.ttIntS G w = (Work.Spaces.w w) ^ 2 * E2s G w := rfl

/-- The honest `H^0`-mass of `∂_θ²G` is nonnegative. -/
theorem ttIntS_nonneg (G : ℝ → ℝ → ℝ) (w : ℝ) : 0 ≤ Work.EllipticEst.Core.ttIntS G w := by
  rw [ttIntS_eq]
  exact mul_nonneg (sq_nonneg _) (e2s_nonneg G w)

/-- **The square root of the slice energy is dominated by the honest `H^0`-mass.**  Since the
radial weight is at least `1`, `√(E2s) = √(ttIntS)/w ≤ √(ttIntS) ≤ 1 + ttIntS`. -/
theorem sqrt_e2s_le_one_add_ttIntS (G : ℝ → ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    Real.sqrt (E2s G w) ≤ 1 + Work.EllipticEst.Core.ttIntS G w := by
  have hww : 1 ≤ Work.Spaces.w w := one_le_w hw
  have hwwpos : 0 < Work.Spaces.w w := w_pos hw
  have hsq : Real.sqrt (Work.EllipticEst.Core.ttIntS G w)
      = Work.Spaces.w w * Real.sqrt (E2s G w) := by
    rw [ttIntS_eq, Real.sqrt_mul (le_of_lt (pow_pos hwwpos 2)) (E2s G w),
      Real.sqrt_sq (le_of_lt hwwpos)]
  have h1 : Real.sqrt (E2s G w)
      = Real.sqrt (Work.EllipticEst.Core.ttIntS G w) / Work.Spaces.w w := by
    rw [hsq, mul_div_cancel_left₀ _ (ne_of_gt hwwpos)]
  have hT0 : 0 ≤ Work.EllipticEst.Core.ttIntS G w := ttIntS_nonneg G w
  calc Real.sqrt (E2s G w) = Real.sqrt (Work.EllipticEst.Core.ttIntS G w) / Work.Spaces.w w := h1
    _ ≤ Real.sqrt (Work.EllipticEst.Core.ttIntS G w) := by
        rw [div_le_iff₀ hwwpos]
        nlinarith [Real.sqrt_nonneg (Work.EllipticEst.Core.ttIntS G w), hww]
    _ ≤ 1 + Work.EllipticEst.Core.ttIntS G w := sqrt_le_one_add_self hT0

/-! ## The two Taylor bounds for a `C²` slice -/

/-- `|∫_a^b (b - t) g t| ≤ (b - a) ∫_a^b |g t|` for a continuous `g`. -/
theorem abs_integral_linear_mul_le {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.uIcc a b)) :
    |∫ t in a..b, (b - t) * g t| ≤ (b - a) * ∫ t in a..b, |g t| := by
  have hcont1 : ContinuousOn (fun t : ℝ => (b - t) * |g t|) (Set.uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).mul hg.abs
  calc |∫ t in a..b, (b - t) * g t| ≤ ∫ t in a..b, |(b - t) * g t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ = ∫ t in a..b, (b - t) * |g t| := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ b - t from by linarith [ht.2])]
    _ ≤ ∫ t in a..b, (b - a) * |g t| := by
        refine intervalIntegral.integral_mono_on hab hcont1.intervalIntegrable
          ((hg.abs.const_mul (b - a)).intervalIntegrable) ?_
        intro t ht
        exact mul_le_mul_of_nonneg_right (by linarith [ht.1]) (abs_nonneg _)
    _ = (b - a) * ∫ t in a..b, |g t| := intervalIntegral.integral_const_mul _ _

/-- **Taylor about the left endpoint.**  For `0 < θ₀ < θ < π/2` and a `C²` slice,
`|f θ - f θ₀ - f' θ₀ (θ - θ₀)| ≤ (θ - θ₀) ∫_{θ₀}^{θ} |f''|`. -/
theorem sliceTaylorLeft {f : ℝ → ℝ} {θ θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hlt : θ₀ < θ)
    (hθ : θ < Real.pi / 2) (hC2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    |f θ - f θ₀ - deriv f θ₀ * (θ - θ₀)| ≤ (θ - θ₀) * ∫ t in θ₀..θ, |deriv (deriv f) t| := by
  have hT := Work.FTS.EllSol.ASlotRoute.Auxiliary.taylorSecondOrderIntegral
    (a := Real.pi / 2) (y := θ₀) (x := θ) (u := f) hθ₀ hlt hθ hC2
  have hEq : f θ - f θ₀ - deriv f θ₀ * (θ - θ₀)
      = ∫ t in θ₀..θ, (θ - t) * deriv (deriv f) t := by
    rw [hT]; ring
  have hcont : ContinuousOn (deriv (deriv f)) (Set.uIcc θ₀ θ) := by
    refine (Work.FTS.EllSol.c2_continuousOn_deriv_deriv hC2).mono ?_
    intro t ht
    rw [Set.uIcc_of_le hlt.le] at ht
    exact ⟨lt_of_lt_of_le hθ₀ ht.1, lt_of_le_of_lt ht.2 hθ⟩
  rw [hEq]
  exact abs_integral_linear_mul_le hlt.le hcont

/-- **Taylor about the right endpoint.**  For `0 < θ < θ₀ < π/2` and a `C²` slice,
`|f θ - f θ₀ - f' θ₀ (θ - θ₀)| ≤ 2 (θ₀ - θ) ∫_{θ}^{θ₀} |f''|`. -/
theorem sliceTaylorRight {f : ℝ → ℝ} {θ θ₀ : ℝ} (hθ : 0 < θ) (hlt : θ < θ₀)
    (hθ₀ : θ₀ < Real.pi / 2) (hC2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    |f θ - f θ₀ - deriv f θ₀ * (θ - θ₀)| ≤ 2 * (θ₀ - θ) * ∫ t in θ..θ₀, |deriv (deriv f) t| := by
  have hT := Work.FTS.EllSol.ASlotRoute.Auxiliary.taylorSecondOrderIntegral
    (a := Real.pi / 2) (y := θ) (x := θ₀) (u := f) hθ hlt hθ₀ hC2
  have hftc : deriv f θ₀ - deriv f θ = ∫ t in θ..θ₀, deriv (deriv f) t :=
    Work.FTS.EllSol.c2_deriv_sub_eq_intervalIntegral hC2 hθ hlt.le hθ₀
  have hEq : f θ - f θ₀ - deriv f θ₀ * (θ - θ₀)
      = (θ₀ - θ) * (∫ t in θ..θ₀, deriv (deriv f) t)
        - ∫ t in θ..θ₀, (θ₀ - t) * deriv (deriv f) t := by
    rw [← hftc, hT]; ring
  have hcont : ContinuousOn (deriv (deriv f)) (Set.uIcc θ θ₀) := by
    refine (Work.FTS.EllSol.c2_continuousOn_deriv_deriv hC2).mono ?_
    intro t ht
    rw [Set.uIcc_of_le hlt.le] at ht
    exact ⟨lt_of_lt_of_le hθ ht.1, lt_of_le_of_lt ht.2 hθ₀⟩
  have hA : |(θ₀ - θ) * (∫ t in θ..θ₀, deriv (deriv f) t)|
      ≤ (θ₀ - θ) * ∫ t in θ..θ₀, |deriv (deriv f) t| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ₀ - θ)]
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral.abs_integral_le_integral_abs hlt.le) (by linarith)
  have hB := abs_integral_linear_mul_le hlt.le hcont
  rw [hEq]
  have htri : |(θ₀ - θ) * (∫ t in θ..θ₀, deriv (deriv f) t)
      - ∫ t in θ..θ₀, (θ₀ - t) * deriv (deriv f) t|
      ≤ |(θ₀ - θ) * (∫ t in θ..θ₀, deriv (deriv f) t)|
        + |∫ t in θ..θ₀, (θ₀ - t) * deriv (deriv f) t| :=
    abs_sub_le_iff.mpr
      ⟨by linarith [le_abs_self ((θ₀ - θ) * ∫ t in θ..θ₀, deriv (deriv f) t),
          neg_le_abs (∫ t in θ..θ₀, (θ₀ - t) * deriv (deriv f) t)],
       by linarith [le_abs_self (∫ t in θ..θ₀, (θ₀ - t) * deriv (deriv f) t),
          neg_le_abs ((θ₀ - θ) * ∫ t in θ..θ₀, deriv (deriv f) t)]⟩
  linarith [htri, hA, hB]

/-! ## The weighted Cauchy–Schwarz bound for the slice energy -/

/-- **`∫_{Iθ} |h| ≤ √(π/2) √(∫_{Iθ} h² σ)`** for the angular weight `σ = sin(2θ)^{-99/100}`. -/
theorem integral_abs_le_sqrt_thEta {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2))) :
    (∫ θ in Set.Icc 0 (Real.pi / 2), |h θ|) ≤ Real.sqrt (Real.pi / 2) *
      Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
        h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) :=
  Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted hint

/-! ## Integrability of the slice of the second derivative -/

/-- The `θ`-slice of `∂_θ²G` at `w` is integrable against `σ` (the constant `(w w)²` is
stripped off the honest hypothesis). -/
theorem integrableOn_second_deriv {G : ℝ → ℝ → ℝ}
    (hhon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) {w : ℝ} (hw : 0 < w) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have h := hhon.1 w hw
  have hc : ((Work.Spaces.w w) ^ 2) ≠ 0 := ne_of_gt (pow_pos (w_pos hw) 2)
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ * ((Work.Spaces.w w) ^ 2)) Work.Spaces.Iθ :=
    h.congr (Filter.Eventually.of_forall (fun θ => by ring))
  refine (h2.mul_const (((Work.Spaces.w w) ^ 2)⁻¹)).congr
    (Filter.Eventually.of_forall (fun θ => ?_))
  simp only
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]

/-- The absolute value of the second derivative of the slice is integrable on `Iθ`. -/
theorem integrableOn_abs_second_deriv {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    (hhon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) {w : ℝ} (hw : 0 < w) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      |Work.Spaces.pth (Work.Spaces.pth G) w θ|) Work.Spaces.Iθ := by
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hbulk : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    hhon.1 w hw
  have hdom := h1.add hbulk
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => |Work.Spaces.pth (Work.Spaces.pth G) w θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => |Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2|)
      ((hsm.pth.pth).continuousOn.abs) hw
  refine hdom.mono' haesm ?_
  filter_upwards [one_le_thEta_ae] with θ hθ1
  have hA0 : 0 ≤ (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 := sq_nonneg _
  have hc1 : 1 ≤ (Work.Spaces.w w) ^ 2 := one_le_w_sq hw
  have hB0 : 0 ≤ (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
      * Work.FTS.EllipticEst.thEta θ :=
    mul_nonneg (mul_nonneg hA0 (by linarith)) (by linarith)
  have hkey : (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
      ≤ (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
        * Work.FTS.EllipticEst.thEta θ := by
    calc (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
        ≤ (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2) :=
          le_mul_of_one_le_right hA0 hc1
      _ ≤ (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
            * Work.FTS.EllipticEst.thEta θ :=
          le_mul_of_one_le_right (mul_nonneg hA0 (by linarith)) hθ1
  have hbd : |Work.Spaces.pth (Work.Spaces.pth G) w θ|
      ≤ 1 + (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
          * Work.FTS.EllipticEst.thEta θ := by
    calc |Work.Spaces.pth (Work.Spaces.pth G) w θ|
        = Real.sqrt ((Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt ((Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
            * Work.FTS.EllipticEst.thEta θ) := Real.sqrt_le_sqrt hkey
      _ ≤ 1 + (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
            * Work.FTS.EllipticEst.thEta θ := sqrt_le_one_add_self hB0
  have hpos : 0 ≤ 1 + (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
      * Work.FTS.EllipticEst.thEta θ := by linarith [hB0]
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_abs, abs_of_nonneg hpos]
  exact hbd

/-! ## The pointwise slice bound -/

/-- **The second-order Taylor slice estimate about `π/4`.** -/
theorem slice_pointwise_le {G : ℝ → ℝ → ℝ} {w θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2)
    (hC2 : ContDiffOn ℝ 2 (fun t : ℝ => G w t) (Set.Ioo 0 (Real.pi / 2)))
    (habs : MeasureTheory.IntegrableOn
      (fun t : ℝ => |deriv (deriv (fun t : ℝ => G w t)) t|) Work.Spaces.Iθ)
    (hCS : (∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t|)
      ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (E2s G w)) :
    |G w θ| ≤ |G w (Real.pi / 4)| + (Real.pi / 4) * |deriv (fun t : ℝ => G w t) (Real.pi / 4)|
      + (Real.pi / 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (E2s G w) := by
  have hπ4pos : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hIθnn : 0 ≤ ∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t| := by
    refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun t _ => abs_nonneg _)
  have hsubI : ∀ {c d : ℝ}, c ≤ d → 0 < c → d < Real.pi / 2 →
      ∫ t in c..d, |deriv (deriv (fun t : ℝ => G w t)) t|
        ≤ ∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t| := by
    intro c d hcd hc hd
    rw [intervalIntegral.integral_of_le hcd]
    refine MeasureTheory.setIntegral_mono_set habs
      (Filter.Eventually.of_forall (fun t => abs_nonneg _)) ?_
    filter_upwards with t ht using ⟨le_of_lt (lt_trans hc ht.1), le_of_lt (lt_of_le_of_lt ht.2 hd)⟩
  -- the Taylor remainder is controlled by `(π/2) ∫_{Iθ} |f''|`
  have hrem : |G w θ - G w (Real.pi / 4)
      - deriv (fun t : ℝ => G w t) (Real.pi / 4) * (θ - Real.pi / 4)|
      ≤ (Real.pi / 2) * ∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t| := by
    rcases lt_trichotomy θ (Real.pi / 4) with hlt | heq | hgt
    · have hT := sliceTaylorRight hθ0 hlt hπ4lt hC2
      have hI := hsubI hlt.le hθ0 hπ4lt
      have hnn : 0 ≤ ∫ t in θ..Real.pi / 4, |deriv (deriv (fun t : ℝ => G w t)) t| :=
        intervalIntegral.integral_nonneg hlt.le (fun t _ => abs_nonneg _)
      refine hT.trans ?_
      refine mul_le_mul ?_ hI hnn (by linarith [Real.pi_pos])
      linarith [hθ0]
    · subst heq
      simp only [sub_self, mul_zero, abs_zero]
      exact mul_nonneg (by linarith [Real.pi_pos]) hIθnn
    · have hT := sliceTaylorLeft hπ4pos hgt hθ1 hC2
      have hI := hsubI hgt.le hπ4pos hθ1
      have hnn : 0 ≤ ∫ t in Real.pi / 4..θ, |deriv (deriv (fun t : ℝ => G w t)) t| :=
        intervalIntegral.integral_nonneg hgt.le (fun t _ => abs_nonneg _)
      refine hT.trans ?_
      refine (mul_le_mul (le_refl _) hI hnn (by linarith [Real.pi_pos])).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [hθ1, Real.pi_pos]) hIθnn
  -- the Taylor remainder is additive, and the linear term is bounded
  have hsplit : G w θ - G w (Real.pi / 4)
      = deriv (fun t : ℝ => G w t) (Real.pi / 4) * (θ - Real.pi / 4)
        + (G w θ - G w (Real.pi / 4)
            - deriv (fun t : ℝ => G w t) (Real.pi / 4) * (θ - Real.pi / 4)) := by ring
  have htri : |G w θ| ≤ |G w (Real.pi / 4)| + |G w θ - G w (Real.pi / 4)| := by
    have h := abs_add_le (G w (Real.pi / 4)) (G w θ - G w (Real.pi / 4))
    rw [add_sub_cancel] at h
    exact h
  have hsec : |G w θ - G w (Real.pi / 4)|
      ≤ (Real.pi / 4) * |deriv (fun t : ℝ => G w t) (Real.pi / 4)|
        + (Real.pi / 2) * ∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t| := by
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add ?_ hrem)
    have hθm : |θ - Real.pi / 4| ≤ Real.pi / 4 := by
      rw [abs_le]
      constructor <;> linarith [hθ0, hθ1, Real.pi_pos]
    rw [abs_mul]
    nlinarith [hθm, abs_nonneg (deriv (fun t : ℝ => G w t) (Real.pi / 4))]
  -- assembly
  have hfin : |G w θ| ≤ |G w (Real.pi / 4)|
      + (Real.pi / 4) * |deriv (fun t : ℝ => G w t) (Real.pi / 4)|
      + (Real.pi / 2) * ∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t| := by
    linarith [htri, hsec]
  refine hfin.trans ?_
  have hstep : (Real.pi / 2) * (∫ t in Work.Spaces.Iθ,
      |deriv (deriv (fun t : ℝ => G w t)) t|)
      ≤ (Real.pi / 2) * (Real.sqrt (Real.pi / 2) * Real.sqrt (E2s G w)) :=
    mul_le_mul_of_nonneg_left hCS (by linarith [Real.pi_pos])
  linarith [hstep]

/-! ## The main theorem -/

theorem mollSliceBound : ∃ C : ℝ, 0 < C ∧ ∀ (G : ℝ → ℝ → ℝ),
    Work.FTS.EllSol.EllPkgAux.TraceClass G → Work.FTS.EllSol.EllPkgAux.FourInts G →
    (∀ w : ℝ, 0 < w → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |G w θ| ≤ C * Work.FTS.EllSol.EllPkgAux.MGf G w) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (Work.FTS.EllSol.EllPkgAux.MGf G) (Set.Icc a b)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro G hT hF
  obtain ⟨hsm, -, -, -, -, -, -, hhon⟩ := hT
  constructor
  · -- ## the pointwise bound
    intro w hw θ hθ0 hθ1
    have hC2 : ContDiffOn ℝ 2 (fun t : ℝ => G w t) (Set.Ioo 0 (Real.pi / 2)) :=
      (hsm.curry_θ hw).of_le (by simp [Work.Stability.smoothOrder])
    have hE2 : MeasureTheory.IntegrableOn (fun t : ℝ =>
        (deriv (deriv (fun t : ℝ => G w t)) t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        Work.Spaces.Iθ := by
      simpa only [Work.Spaces.pth] using integrableOn_second_deriv hhon hw
    have habs : MeasureTheory.IntegrableOn (fun t : ℝ =>
        |deriv (deriv (fun t : ℝ => G w t)) t|) Work.Spaces.Iθ := by
      simpa only [Work.Spaces.pth] using integrableOn_abs_second_deriv hsm hhon hw
    have hE2' : MeasureTheory.IntegrableOn (fun t : ℝ =>
        (deriv (deriv (fun t : ℝ => G w t)) t) ^ 2 * (Real.sin (2 * t)) ^ (-(99 / 100 : ℝ)))
        (Set.Icc 0 (Real.pi / 2)) := by
      simpa only [Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta, Work.Spaces.eta] using hE2
    have hE2s_eq : E2s G w = ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
        (deriv (deriv (fun t : ℝ => G w t)) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)) := by
      simp only [E2s, Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta, Work.Spaces.eta,
        Work.Spaces.pth]
    have hCS : (∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t|)
        ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (E2s G w) := by
      have h := integral_abs_le_sqrt_thEta hE2'
      rw [← hE2s_eq] at h
      simpa only [Work.Spaces.Iθ] using h
    have hbound := slice_pointwise_le hθ0 hθ1 hC2 habs hCS
    have hsp : Work.Spaces.pth G w (Real.pi / 4) = deriv (fun t : ℝ => G w t) (Real.pi / 4) :=
      rfl
    rw [← hsp] at hbound
    -- the numerical comparison
    have hπ4 : (Real.pi / 4 : ℝ) ≤ 4 := by linarith [Real.pi_lt_four]
    have hsqrtpi : Real.sqrt (Real.pi / 2) ≤ 2 := by
      calc Real.sqrt (Real.pi / 2) ≤ Real.sqrt ((2 : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
        _ = 2 := Real.sqrt_sq (by norm_num)
    have hc3 : (Real.pi / 2) * Real.sqrt (Real.pi / 2) ≤ 4 := by
      have h1 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
      calc (Real.pi / 2) * Real.sqrt (Real.pi / 2) ≤ 2 * 2 :=
            mul_le_mul h1 hsqrtpi (Real.sqrt_nonneg _) (by norm_num)
        _ = 4 := by norm_num
    have hb0 : |G w (Real.pi / 4)| ≤ 4 * MGf G w := by
      rw [MGf]
      nlinarith [abs_nonneg (G w (Real.pi / 4)), abs_nonneg (Work.Spaces.pth G w (Real.pi / 4)),
        Real.sqrt_nonneg (E2s G w)]
    rw [MGf]
    have hBnd1 := mul_le_mul_of_nonneg_right hπ4
      (abs_nonneg (Work.Spaces.pth G w (Real.pi / 4)))
    have hBnd2 := mul_le_mul_of_nonneg_right hc3 (Real.sqrt_nonneg (E2s G w))
    linarith [hbound, hBnd1, hBnd2, abs_nonneg (G w (Real.pi / 4)),
      abs_nonneg (Work.Spaces.pth G w (Real.pi / 4)), Real.sqrt_nonneg (E2s G w)]
  · -- ## local integrability of `MGf`
    intro a b ha hab
    have hπ4pos : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
    have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
    have hsubIoi : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun w hw => lt_of_lt_of_le ha hw.1
    have hsubIz : Set.Icc a b ⊆ Work.Spaces.Iz := fun w hw => le_trans ha.le hw.1
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
      MeasureTheory.integrableOn_const
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    have h2 : MeasureTheory.IntegrableOn (fun w : ℝ => |G w (Real.pi / 4)|) (Set.Icc a b) :=
      (((hsm.curry_z ⟨hπ4pos, hπ4lt⟩).continuousOn.mono hsubIoi).abs).integrableOn_compact
        isCompact_Icc
    have h3 : MeasureTheory.IntegrableOn (fun w : ℝ => |Work.Spaces.pth G w (Real.pi / 4)|)
        (Set.Icc a b) :=
      ((((hsm.pth).curry_z ⟨hπ4pos, hπ4lt⟩).continuousOn.mono hsubIoi).abs).integrableOn_compact
        isCompact_Icc
    have h4 : MeasureTheory.IntegrableOn (fun w : ℝ => Real.sqrt (E2s G w)) (Set.Icc a b) := by
      have htt : MeasureTheory.IntegrableOn (fun w : ℝ => Work.EllipticEst.Core.ttIntS G w)
          (Set.Icc a b) := hF.2.2.1.mono_set hsubIz
      have hdom : MeasureTheory.IntegrableOn
          (fun w : ℝ => 1 + Work.EllipticEst.Core.ttIntS G w) (Set.Icc a b) := h1.add htt
      have haesm : MeasureTheory.AEStronglyMeasurable (fun w : ℝ => Real.sqrt (E2s G w))
          (MeasureTheory.volume.restrict (Set.Icc a b)) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable
          (Work.FTS.EllSol.EllPkgAux.MollAux.aesmE2s hsm ha)
      refine hdom.mono' haesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with w hw
      have hpos : 0 ≤ 1 + Work.EllipticEst.Core.ttIntS G w := by
        linarith [ttIntS_nonneg G w]
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (E2s G w)),
        abs_of_nonneg hpos]
        using sqrt_e2s_le_one_add_ttIntS G (lt_of_lt_of_le ha hw.1)
    have hsum : MeasureTheory.IntegrableOn (fun w : ℝ => 1 + |G w (Real.pi / 4)|
        + |Work.Spaces.pth G w (Real.pi / 4)| + Real.sqrt (E2s G w)) (Set.Icc a b) :=
      ((h1.add h2).add h3).add h4
    have hEq : MGf G = fun w : ℝ => 1 + |G w (Real.pi / 4)|
        + |Work.Spaces.pth G w (Real.pi / 4)| + Real.sqrt (E2s G w) := by
      funext w
      rfl
    rw [hEq]
    exact hsum

end Work.FTS.EllSol.EllPkgAux
