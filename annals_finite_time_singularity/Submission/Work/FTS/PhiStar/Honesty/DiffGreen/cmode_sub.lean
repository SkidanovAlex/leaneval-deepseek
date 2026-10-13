import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty.DiffGreen

/-- The elementary AM–GM estimate `|a·b·c| ≤ (a²c + b²c)/2` for a nonnegative weight `c`
applied to the split `a·b·c = (a√c)·(b√c)`.  It is the pointwise bound by which the slice
integrand `F z θ · e_m θ · cos θ` is dominated by the sum of the two integrable squares
`(F z θ)² cos θ` and `e_m θ² cos θ`. -/
lemma cmode_abs_mul_mul_le (a b c : ℝ) (hc : 0 ≤ c) :
    |a * b * c| ≤ (a ^ 2 * c + b ^ 2 * c) / 2 := by
  have h1 : |a * b * c| = |a| * |b| * c := by rw [abs_mul, abs_mul, abs_of_nonneg hc]
  rw [h1]
  have h2 : 2 * |a| * |b| ≤ |a| ^ 2 + |b| ^ 2 := two_mul_le_add_sq |a| |b|
  have h3 : (2 * |a| * |b|) * c ≤ (|a| ^ 2 + |b| ^ 2) * c :=
    mul_le_mul_of_nonneg_right h2 hc
  rw [sq_abs, sq_abs] at h3
  linarith [h3]

/-- **The slice integrand is integrable on `Iθ`.**  For `F` smooth on the open quadrant and
`F ∈ ℋ^0` (`Work.Spaces.HkMem α 0 F`), every mode-weighted slice `θ ↦ F z θ · e_m θ · cos θ`
(`z > 0`) is integrable over `Iθ`.

`Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem` gives the integrability of
`θ ↦ (F z θ)² cos θ`; the second square `θ ↦ e_m θ² cos θ` is continuous on the compact `Iθ`,
hence integrable; the pointwise AM–GM bound `cmode_abs_mul_mul_le` (legitimate on `Iθ`, where
`cos θ ≥ 0`) transfers integrability, using that the product is a.e. strongly measurable since
its uncurried form is continuous on the open quadrant
(`Work.Spaces.aesm_slice_of_continuousOn_Qd`). -/
lemma cmode_integrableOn_mul_eFam_cos {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 0 F)
    (m : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      Work.Spaces.Iθ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- the two squares `(F z ·)² cos` and `e_m² cos` are integrable on `Iθ`
  have hA : IntegrableOn (fun θ : ℝ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem hmem hz
  have hB : IntegrableOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      Work.Spaces.Iθ := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    exact (((Work.EllipticEst.ModalSolution.continuous_eFam m).pow 2).mul
      Real.continuous_cos).continuousOn
  -- their half-sum dominates the integrand pointwise
  have hdom : IntegrableOn (fun θ : ℝ => ((F z θ) ^ 2 * Real.cos θ
      + (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ) / 2) Work.Spaces.Iθ := by
    have h := (hA.add hB).div_const 2
    show Integrable (fun θ : ℝ => ((F z θ) ^ 2 * Real.cos θ
      + (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ) / 2)
      (volume.restrict Work.Spaces.Iθ)
    simpa only [Pi.add_apply, div_eq_mul_inv] using h
  -- a.e. strong measurability: the uncurried integrand is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2
      * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
      (hF.forall 0).continuousOn
    have h2 : Continuous (fun p : ℝ × ℝ =>
        Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2) :=
      ((Work.EllipticEst.ModalSolution.continuous_eFam m).comp continuous_snd).mul
        (Real.continuous_cos.comp continuous_snd)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2
        * (Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2)) Work.FTS.EllipticEst.Q0 :=
      h1.mul h2.continuousOn
    convert h3 using 1
    funext p
    ring
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
  refine hdom.mono' haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hIθ] with θ hθ
  have hc : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  rw [Real.norm_eq_abs]
  exact cmode_abs_mul_mul_le _ _ _ hc

/-- The interval-integral form (`0` to `π/2`) of `cmode_integrableOn_mul_eFam_cos`: the slice
integrand of the mode coefficient is interval integrable. -/
lemma cmode_intervalIntegrable_mul_eFam_cos {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 0 F)
    (m : ℕ) {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (fun θ : ℝ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Real.cos θ) volume 0 (Real.pi / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  exact cmode_integrableOn_mul_eFam_cos hF hmem m hz

/-- **The mode coefficients are additive in the source** (at `z > 0`, where the slice integral
is taken over `θ ∈ Iθ = [0, π/2]` against the continuous weight `eFam m θ · cos θ`).

The only analytic input is the `θ`-integrability of `X z θ · eFam m θ · cos θ` and of
`Y z θ · eFam m θ · cos θ` on `Iθ`: it follows from `Work.Spaces.HkMem α 0 X` via
`Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem` together with the pointwise bound
`|f · e_m cos| ≤ (f² · cos + e_m² · cos)/2` and `∫_θ eFam m θ² cos θ = eNorm m < ∞`
(`Work.EllipticEst.ModalSolution.eNorm_pos`).  The denominator `∫_θ eFam m θ² cos θ` is nonzero
(`eNorm_pos`), so plain subtraction of the two `intervalIntegral`s closes the identity. -/
theorem cmode_sub {α : ℝ} {X Y : ℝ → ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X) (hY : Work.FTS.EllipticEst.SmoothOpen Y)
    (hmX : Work.Spaces.HkMem α 0 X) (hmY : Work.Spaces.HkMem α 0 Y)
    (m : ℕ) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Series.cmode m (fun z θ => X z θ - Y z θ) z
      = Work.FTS.PhiStar.Series.cmode m X z - Work.FTS.PhiStar.Series.cmode m Y z := by
  -- the two slice integrands are interval integrable
  have hXint := cmode_intervalIntegrable_mul_eFam_cos hX hmX m hz
  have hYint := cmode_intervalIntegrable_mul_eFam_cos hY hmY m hz
  -- hence the numerator of the `X - Y` mode is the difference of the numerators
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (X z θ - Y z θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 2),
          X z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        - ∫ θ in (0 : ℝ)..(Real.pi / 2),
            Y z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
    rw [show (fun θ : ℝ => (X z θ - Y z θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Real.cos θ)
        = fun θ : ℝ => X z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ
            - Y z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ from
      funext fun θ => by ring]
    exact intervalIntegral.integral_sub hXint hYint
  -- the three `cmode`s share the same denominator `∫ e_m² cos`
  simp only [Work.FTS.PhiStar.Series.cmode]
  rw [hnum, sub_div]

end Work.FTS.PhiStar.Honesty.DiffGreen
