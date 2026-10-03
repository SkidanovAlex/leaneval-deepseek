import Mathlib
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.DivisorBasics
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.weyl_surface
import Submission.Lib.Unif2.Work.Analysis.Complex.PolePush.pole_push
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Lib.Unif2.Work.Analysis.Complex.Hormander.weightedMeasure
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.integral_dbar_eq_zero
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.integral_comp_normSq
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.cauchyPompeiu
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.dbar_representation
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.dbar_solvable

namespace Work.Analysis.RiemannSurface

/-- **Geometric expansion of the Cauchy kernel off the disc of radius `‖z‖`.**  For `‖z‖ < ‖w‖` the
kernel `(z - w)⁻¹` is the sum of the (convergent) geometric series `Σ_m w⁻¹ (z/w)^m`.  This is the
tool the moments argument uses to turn a circle integral against `(z-w)⁻¹` into the moments
`∮ z^m f z`; the uniform bound `‖w⁻¹ (z/w)^m‖ ≤ ‖w‖⁻¹ (‖z‖/‖w‖)^m` on a circle of radius `r < ‖w‖`
makes the corresponding series of integrals summable. -/
theorem hasSum_cauchyKernel {z w : ℂ} (hzw : ‖z‖ < ‖w‖) :
    HasSum (fun m : ℕ => w⁻¹ * (z / w) ^ m) (-(z - w)⁻¹) := by
  have hw : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hzw
    exact absurd hzw (not_lt_of_ge (norm_nonneg z))
  have hξ : ‖z / w‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hw)]
    exact hzw
  have h1 : HasSum (fun m : ℕ => w⁻¹ * (z / w) ^ m) (w⁻¹ * (1 - z / w)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hξ).mul_left w⁻¹
  have h2 : w⁻¹ * (1 - z / w)⁻¹ = -(z - w)⁻¹ := by
    rw [show z - w = -(w - z) from by ring, inv_neg, neg_neg]
    have hA : (1 : ℂ) - z / w = (w - z) / w := by field_simp
    rw [hA, inv_div, mul_comm]
    field_simp
  rwa [h2] at h1

/-- **The outer Cauchy-kernel term bound.**  For `‖z‖ = r < ‖w‖`,
`‖(-w⁻¹) (z/w)^m f z‖ ≤ ‖f z‖ (r/‖w‖)^m ‖w‖⁻¹` — indeed equality: the `w⁻¹` contributes `‖w‖⁻¹`,
the `m`-th power contributes `(r/‖w‖)^m`, and the rest is `‖f z‖`.  This is the pointwise
domination input of the outer Cauchy-kernel expansion (no conditional `simp` needed: plain `rw`). -/
theorem norm_cauchyKernel_term_le {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) {w : ℂ}
    (hwr : r < ‖w‖) {z : ℂ} (hz : ‖z‖ = r) (m : ℕ) :
    ‖(-w⁻¹) * (z / w) ^ m * f z‖ ≤ ‖f z‖ * (r / ‖w‖) ^ m * ‖w‖⁻¹ := by
  have hw : (0 : ℝ) < ‖w‖ := hr.trans_lt hwr
  rw [norm_mul, norm_mul, norm_neg, norm_inv, norm_pow, norm_div, hz, div_pow]
  exact le_of_eq (by ring)

/-- **The norm of the derivative of the circle map.**  `‖deriv (circleMap 0 r) θ‖ = |r|`; this is
the factor `r` that appears when the outer Cauchy-kernel expansion is applied to a circle integral.
(The companion identity `‖circleMap 0 r θ‖ = |r|` is Mathlib's `norm_circleMap_zero`.) -/
theorem norm_deriv_circleMap_eq (r : ℝ) (θ : ℝ) :
    ‖deriv (circleMap 0 r) θ‖ = |r| := by
  rw [show deriv (circleMap 0 r) θ = circleMap 0 r θ * Complex.I from
    (hasDerivAt_circleMap (0 : ℂ) r θ).deriv]
  rw [norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]

/-- **The outer Cauchy-kernel expansion.**  For `r < ‖w‖` the circle integral of `(z-w)⁻¹ f z`
expands as the (summable) series of moments against `-w⁻¹ (z/w)^m`.  Mathlib has the inner case
(`Complex.hasSum_two_pi_I_cauchyPowerSeries_integral`); this is the outer one, which is what the
moments argument on the punctured disc needs.  The measurability hypothesis on `f ∘ circleMap` is
automatic for `CircleIntegrable f 0 r` (divide out the nowhere-vanishing `deriv`). -/
theorem hasSum_circleIntegral_cauchyKernel {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hwr : r < ‖w‖) (hf : CircleIntegrable f 0 r)
    (hf' : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => f (circleMap 0 r θ))
      (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi)))) :
    HasSum (fun m : ℕ => ∮ z in C(0, r), (-w⁻¹) * (z / w) ^ m * f z)
      (∮ z in C(0, r), (z - w)⁻¹ * f z) := by
  have hwpos : 0 < ‖w‖ := lt_trans hr hwr
  have hrle : (0 : ℝ) ≤ r := hr.le
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 r θ‖ = r := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr]
  have hw : w ≠ 0 := norm_pos_iff.mp hwpos
  have hlt : r / ‖w‖ < 1 := (div_lt_one hwpos).mpr hwr
  have h0 : (0 : ℝ) ≤ r / ‖w‖ := div_nonneg hrle hwpos.le
  simp only [circleIntegral]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := 2 * Real.pi)
    (μ := MeasureTheory.volume)
    (F := fun (m : ℕ) (θ : ℝ) =>
      deriv (circleMap 0 r) θ • ((-w⁻¹) * (circleMap 0 r θ / w) ^ m * f (circleMap 0 r θ)))
    (f := fun θ : ℝ => deriv (circleMap 0 r) θ • ((circleMap 0 r θ - w)⁻¹ * f (circleMap 0 r θ)))
    (fun (m : ℕ) (θ : ℝ) => ‖f (circleMap 0 r θ)‖ * (r / ‖w‖) ^ m * (r * ‖w‖⁻¹)) ?_ ?_ ?_ ?_ ?_
  · intro m
    have hconst : MeasureTheory.AEStronglyMeasurable (fun _ : ℝ => (-w⁻¹ : ℂ))
        (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := MeasureTheory.aestronglyMeasurable_const
    have hc : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => circleMap 0 r θ / w)
        (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by fun_prop
    have hmul : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (-w⁻¹) * (circleMap 0 r θ / w) ^ m * f (circleMap 0 r θ))
        (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := (hconst.mul (hc.pow m)).mul hf'
    have hd : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => deriv (circleMap 0 r) θ)
        (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by fun_prop
    exact hd.smul hmul
  · intro m
    filter_upwards with θ hθ
    rw [norm_smul, norm_deriv_circleMap_eq]
    calc |r| * ‖(-w⁻¹) * (circleMap 0 r θ / w) ^ m * f (circleMap 0 r θ)‖
        ≤ r * (‖f (circleMap 0 r θ)‖ * (r / ‖w‖) ^ m * ‖w‖⁻¹) := by
          rw [abs_of_pos hr]
          exact mul_le_mul_of_nonneg_left (norm_cauchyKernel_term_le hrle hwr (hnorm θ) m) hrle
      _ = ‖f (circleMap 0 r θ)‖ * (r / ‖w‖) ^ m * (r * ‖w‖⁻¹) := by ring
  · refine Filter.Eventually.of_forall fun t _ => ?_
    exact ((summable_geometric_of_lt_one h0 hlt).mul_left ‖f (circleMap 0 r t)‖).mul_right
      (r * ‖w‖⁻¹)
  · have hh : IntervalIntegrable (fun t : ℝ => ‖f (circleMap 0 r t)‖) MeasureTheory.volume 0 (2 * Real.pi) :=
      hf.norm
    simpa only [mul_assoc, tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one h0 hlt] using
      hh.mul_continuousOn continuousOn_const
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    have h := ((hasSum_cauchyKernel (z := circleMap 0 r θ) (w := w)
      (by rw [hnorm θ]; exact hwr)).neg.mul_right (f (circleMap 0 r θ)))
    simpa only [smul_eq_mul, neg_mul, neg_neg] using h.mul_left (deriv (circleMap 0 r) θ)

/-- **Every term of the outer Cauchy-kernel expansion vanishes when the moments do.**  For
`w ≠ 0` and a vanishing moment `∮ z^m f z = 0`, the corresponding term of
`hasSum_circleIntegral_cauchyKernel` vanishes too: the term is the constant
`(-w⁻¹) * (w⁻¹)^m` times that moment. -/
theorem circleIntegral_cauchyKernel_term_eq_zero {f : ℂ → ℂ} {r : ℝ} {w : ℂ} (hw : w ≠ 0) (m : ℕ)
    (hmom : (∮ z in C(0, r), z ^ m * f z) = 0) :
    (∮ z in C(0, r), (-w⁻¹) * (z / w) ^ m * f z) = 0 := by
  have hfun : (fun z : ℂ => (-w⁻¹) * (z / w) ^ m * f z)
      = fun z : ℂ => ((-w⁻¹) * (w⁻¹) ^ m) * (z ^ m * f z) := by
    funext z
    rw [div_eq_mul_inv, mul_pow]
    ring
  rw [hfun]
  have hpull : (∮ z in C(0, r), ((-w⁻¹) * (w⁻¹) ^ m) * (z ^ m * f z))
      = ((-w⁻¹) * (w⁻¹) ^ m) * (∮ z in C(0, r), z ^ m * f z) := by
    simp only [circleIntegral]
    rw [show (fun θ : ℝ => deriv (circleMap 0 r) θ •
          (((-w⁻¹) * (w⁻¹) ^ m) * ((circleMap 0 r θ) ^ m * f (circleMap 0 r θ))))
        = fun θ : ℝ => ((-w⁻¹) * (w⁻¹) ^ m) *
            (deriv (circleMap 0 r) θ * ((circleMap 0 r θ) ^ m * f (circleMap 0 r θ))) from by
      funext θ
      simp only [smul_eq_mul]
      ring]
    simp only [smul_eq_mul]
    rw [intervalIntegral.integral_const_mul]
  rw [hpull, hmom, mul_zero]

/-- **Step 3 of the moments plan.**  If every moment `∮ z^m f z` vanishes and `r < ‖w‖`, then the
outer Cauchy-kernel integral `∮ (z-w)⁻¹ f z` over the circle of radius `r` vanishes: it is the sum of
the expansion terms, all of which are constants times the vanishing moments. -/
theorem circleIntegral_cauchyKernel_eq_zero {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hwr : r < ‖w‖) (hf : CircleIntegrable f 0 r)
    (hf' : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => f (circleMap 0 r θ))
      (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))))
    (hmom : ∀ m : ℕ, (∮ z in C(0, r), z ^ m * f z) = 0) :
    (∮ z in C(0, r), (z - w)⁻¹ * f z) = 0 := by
  have hw : w ≠ 0 := norm_pos_iff.mp (lt_trans hr hwr)
  have hsum := hasSum_circleIntegral_cauchyKernel hr hwr hf hf'
  have hzero : ∀ m : ℕ, (∮ z in C(0, r), (-w⁻¹) * (z / w) ^ m * f z) = 0 :=
    fun m => circleIntegral_cauchyKernel_term_eq_zero hw m (hmom m)
  rw [← hsum.tsum_eq]
  simp only [hzero, tsum_zero]

end Work.Analysis.RiemannSurface
