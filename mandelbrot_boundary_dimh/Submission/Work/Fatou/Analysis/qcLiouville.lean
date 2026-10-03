import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Analysis.fderiv_det_eq
import Submission.Work.Fatou.Analysis.fderiv_norm_le
import Submission.Work.Fatou.Analysis.exists_sphere_points_far
import Submission.Work.Fatou.Analysis.slice_lower_bound
import Submission.Work.Fatou.Analysis.lintegral_annulus_eq_polar
import Submission.Work.Fatou.Analysis.lintegral_normSq_fderiv_le

/-!
# QCLiouville: a bounded injective C^1 quasiconformal map of the plane does not exist

This is FX6 of the FATOU area (see `NOTES_LEAD_fatou.md` and `Submission/Work/Fatou/fatouU.lean`).
It is used to exclude the upper half plane case in the uniformization step of the construction of
perturbed Fatou coordinates (Shishikura, Prop. A.2.1).

Mathematical proof (length-area, up to universal constants).  Let `g : ℂ → ℂ` be injective and
`C¹`, with `dz g` nowhere zero and `‖dzbar g z‖ ≤ k ‖dz g z‖` for a fixed `k < 1`, and `‖g z‖ ≤ M`.
Writing `a z = dz g z`, `b z = dzbar g z` and `L z = fderiv ℝ g z`, the Wirtinger decomposition
`L z v = v * a z + star v * b z` gives

* `(L z).det = ‖a z‖^2 - ‖b z‖^2` (the real Jacobian),
* `‖L z‖ ≤ ‖a z‖ + ‖b z‖`,

hence, with `C = (1+k)/(1-k)`, the pointwise bound `‖L z‖^2 ≤ C * |det (L z)|`: the map is uniformly
quasiconformal with `det > 0`, so it is a local diffeomorphism and (being injective) an open map.

For `r ≥ 1` the boundary `g '' sphere 0 r` of the topological disc `g '' closedBall 0 r` separates
`g 1` from `g (-1)`, so it has diameter at least `d := dist (g 1) (g (-1)) > 0`.  Cauchy–Schwarz
along the curve `θ ↦ g (r e^{iθ})` then gives `d^2 / (2πr) ≤ ∫_(-π)^π r ‖L (r e^{iθ})‖^2 dθ`.
Integrating over `r ∈ [1,R]` and switching to polar coordinates,

  `(d^2/2π) log R ≤ ∫_(annulus) ‖L‖^2 ≤ C ∫_(annulus) |det L| ≤ C * volume (g '' ball 0 R) ≤ C π M^2`,

which is impossible for large `R`.  ∎

The geometric/measure-theoretic inputs are the modules imported above (each proved separately).
-/

open MeasureTheory Metric
open scoped ENNReal Topology

namespace Work.Fatou.Analysis

theorem qcLiouville : MandelDim.QCLiouville := by
  intro g k M hk hC1 hinj hdz hqc hbdd
  have hk0 : 0 ≤ k := by
    have h := hqc 0
    have ha : 0 < ‖MandelDim.dz g 0‖ := norm_pos_iff.mpr (hdz 0)
    have hb : 0 ≤ ‖MandelDim.dzbar g 0‖ := norm_nonneg _
    nlinarith [h, ha, hb]
  have hkm : 0 < 1 - k := by linarith
  have hCqpos : 0 < (1 + k) / (1 - k) := div_pos (by linarith) hkm
  have hdet_eq : ∀ z, (fderiv ℝ g z).det
      = ‖MandelDim.dz g z‖ ^ 2 - ‖MandelDim.dzbar g z‖ ^ 2 := by
    intro z
    simpa [MandelDim.dz, MandelDim.dzbar] using fderiv_det_eq (fderiv ℝ g z)
  have hdetpos : ∀ z, 0 < (fderiv ℝ g z).det := by
    intro z
    have hb : ‖MandelDim.dzbar g z‖ ≤ k * ‖MandelDim.dz g z‖ := hqc z
    have ha : 0 < ‖MandelDim.dz g z‖ := norm_pos_iff.mpr (hdz z)
    have hb2 : ‖MandelDim.dzbar g z‖ ^ 2 ≤ k ^ 2 * ‖MandelDim.dz g z‖ ^ 2 := by
      nlinarith [hb, norm_nonneg (MandelDim.dzbar g z), ha, hk0]
    have hk2 : k ^ 2 < 1 := by nlinarith [hk, hk0]
    rw [hdet_eq z]
    have hprod : 0 < (1 - k ^ 2) * ‖MandelDim.dz g z‖ ^ 2 :=
      mul_pos (by linarith) (pow_pos ha 2)
    nlinarith [hb2, hprod]
  have hpt : ∀ z, ‖fderiv ℝ g z‖ ^ 2 ≤ ((1 + k) / (1 - k)) * (fderiv ℝ g z).det := by
    intro z
    have hb : ‖MandelDim.dzbar g z‖ ≤ k * ‖MandelDim.dz g z‖ := hqc z
    have ha : 0 < ‖MandelDim.dz g z‖ := norm_pos_iff.mpr (hdz z)
    have hnorm := fderiv_norm_le (fderiv ℝ g z)
    simp only [MandelDim.dz, MandelDim.dzbar] at hnorm hb
    have hnorm' : ‖fderiv ℝ g z‖ ≤ (1 + k) * ‖(fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2‖ := by
      nlinarith [hnorm, hb, hk0, norm_nonneg ((fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) / 2)]
    have hsq : ‖fderiv ℝ g z‖ ^ 2
        ≤ (1 + k) ^ 2 * ‖(fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2 := by
      nlinarith [hnorm', norm_nonneg (fderiv ℝ g z), hk0]
    have hbk : ‖(fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2
        ≤ k ^ 2 * ‖(fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2 := by
      nlinarith [hb, norm_nonneg ((fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) / 2), ha, hk0]
    have hstep1 : (1 - k ^ 2) * ‖(fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2
        ≤ ‖(fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2
          - ‖(fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2 := by
      nlinarith [hbk]
    have hstep2 : ((1 + k) / (1 - k))
        * ((1 - k ^ 2) * ‖(fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2)
        ≤ ((1 + k) / (1 - k))
          * (‖(fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2
             - ‖(fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hstep1 (le_of_lt hCqpos)
    have hstep3 : ((1 + k) / (1 - k))
        * ((1 - k ^ 2) * ‖(fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2)
        = (1 + k) ^ 2 * ‖(fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2‖ ^ 2 := by
      field_simp
      ring
    rw [hdet_eq z, MandelDim.dz, MandelDim.dzbar]
    linarith [hsq, hstep2, hstep3]
  have hinj_deriv : ∀ z, Function.Injective (fderiv ℝ g z) := by
    intro z
    have hker : (fderiv ℝ g z).ker = ⊥ := by
      by_contra h
      exact (ne_of_gt (hdetpos z)) (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
    intro a b hab
    have h1 : (fderiv ℝ g z) (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 : a - b ∈ (fderiv ℝ g z).ker := h1
    rw [hker] at h2
    exact sub_eq_zero.mp (by simpa using h2)
  set d : ℝ := dist (g 1) (g (-1)) with hddef
  have hdpos : 0 < d := by
    rw [hddef, dist_pos]
    intro h
    exact (by norm_num : (1:ℂ) ≠ -1) (hinj h)
  have hB : ∀ r : ℝ, 1 ≤ r → ∃ z₁ ∈ Metric.sphere (0:ℂ) r, ∃ z₂ ∈ Metric.sphere (0:ℂ) r,
      d ≤ dist (g z₁) (g z₂) := by
    intro r hr
    have h := exists_sphere_points_far g r hr hC1 hinj hinj_deriv
    rwa [hddef]
  have hM : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hbdd 0)
  set C₀ : ℝ := ((1 + k) / (1 - k)) * (M + 1) ^ 2 * Real.pi with hC0def
  have hC0 : 0 ≤ C₀ := by rw [hC0def]; positivity
  have key : ∀ R : ℝ, 1 ≤ R →
      ENNReal.ofReal (d ^ 2 / (2 * Real.pi)) * ENNReal.ofReal (Real.log R) ≤ ENNReal.ofReal C₀ := by
    intro R hR
    have hmono : ∫⁻ r in Set.Icc (1:ℝ) R, ENNReal.ofReal (d ^ 2 / (2 * Real.pi * r)) ≤
        ∫⁻ r in Set.Icc (1:ℝ) R,
          ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
            ENNReal.ofReal r * ENNReal.ofReal (‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hr
      have hr1 : 1 ≤ r := hr.1
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
      have hslice := slice_lower_bound g d r hr1 (le_of_lt hdpos) hC1 (hB r hr1)
      have hcongr : ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
            ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2)
          = ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
            ENNReal.ofReal r * ENNReal.ofReal (‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2) := by
        apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
        intro θ hθ
        simp only []
        rw [ENNReal.ofReal_mul (le_of_lt hrpos)]
      rw [hcongr] at hslice
      exact hslice
    have hlin1 : ∫⁻ r in Set.Icc (1:ℝ) R, ENNReal.ofReal (d ^ 2 / (2 * Real.pi * r))
        = ENNReal.ofReal (d ^ 2 / (2 * Real.pi)) * ENNReal.ofReal (Real.log R) := by
      have hcongr : Set.EqOn (fun r => ENNReal.ofReal (d ^ 2 / (2 * Real.pi * r)))
          (fun r => ENNReal.ofReal (d ^ 2 / (2 * Real.pi)) * ENNReal.ofReal r⁻¹) (Set.Icc 1 R) := by
        intro r hr
        simp only []
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ d ^ 2 / (2 * Real.pi))]
        congr 1
        field_simp
      rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Icc hcongr]
      rw [MeasureTheory.lintegral_const_mul _ (Measurable.ennreal_ofReal measurable_inv)]
      congr 1
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
      · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR,
          integral_inv (by rw [Set.uIcc_of_le hR]; intro h; linarith [h.1])]
        simp
      · exact ContinuousOn.integrableOn_compact isCompact_Icc
          (ContinuousOn.inv₀ continuousOn_id (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)))
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
        exact inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le zero_lt_one hx.1))
    have hFmeas : Measurable (fun z : ℂ => ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2)) :=
      Measurable.ennreal_ofReal (((hC1.continuous_fderiv (by norm_num)).norm.pow 2).measurable)
    have hann : ∫⁻ r in Set.Icc (1:ℝ) R,
            ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
              ENNReal.ofReal r * ENNReal.ofReal (‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2)
        = ∫⁻ z in Metric.closedBall (0:ℂ) R \ Metric.ball (0:ℂ) 1,
              ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2) :=
      (lintegral_annulus_eq_polar (fun z => ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2)) hFmeas R hR).symm
    have hsub : ∫⁻ z in Metric.closedBall (0:ℂ) R \ Metric.ball (0:ℂ) 1,
            ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2)
        ≤ ∫⁻ z in Metric.ball (0:ℂ) (R + 1), ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2) := by
      apply MeasureTheory.lintegral_mono_set
      intro z hz
      simp only [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right] at hz ⊢
      linarith [hz.1]
    have hE := lintegral_normSq_fderiv_le g ((1 + k) / (1 - k)) (R + 1) (le_of_lt hCqpos) hC1 hinj hpt
    have hvol : MeasureTheory.volume (g '' Metric.ball (0:ℂ) (R + 1))
        ≤ MeasureTheory.volume (Metric.ball (0:ℂ) (M + 1)) := by
      apply MeasureTheory.measure_mono
      rintro w ⟨z, hz, rfl⟩
      simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
      linarith [hbdd z, hM]
    have hvolval : ENNReal.ofReal ((1 + k) / (1 - k)) * MeasureTheory.volume (Metric.ball (0:ℂ) (M + 1))
        = ENNReal.ofReal C₀ := by
      have hpiv : ((NNReal.pi : NNReal) : ENNReal) = ENNReal.ofReal Real.pi := by
        rw [ENNReal.coe_nnreal_eq]
        norm_num
      rw [Complex.volume_ball, hpiv]
      rw [← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ M + 1)]
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (M + 1) ^ 2)]
      rw [← ENNReal.ofReal_mul (le_of_lt hCqpos)]
      congr 1
      rw [hC0def]
      ring
    calc ENNReal.ofReal (d ^ 2 / (2 * Real.pi)) * ENNReal.ofReal (Real.log R)
        = ∫⁻ r in Set.Icc (1:ℝ) R, ENNReal.ofReal (d ^ 2 / (2 * Real.pi * r)) := hlin1.symm
      _ ≤ ∫⁻ r in Set.Icc (1:ℝ) R,
            ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
              ENNReal.ofReal r * ENNReal.ofReal (‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ ^ 2) := hmono
      _ = ∫⁻ z in Metric.closedBall (0:ℂ) R \ Metric.ball (0:ℂ) 1,
              ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2) := hann
      _ ≤ ∫⁻ z in Metric.ball (0:ℂ) (R + 1), ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2) := hsub
      _ ≤ ENNReal.ofReal ((1 + k) / (1 - k)) * MeasureTheory.volume (g '' Metric.ball (0:ℂ) (R + 1)) := hE
      _ ≤ ENNReal.ofReal ((1 + k) / (1 - k)) * MeasureTheory.volume (Metric.ball (0:ℂ) (M + 1)) := by
            gcongr
      _ = ENNReal.ofReal C₀ := hvolval
  have hexp : 0 < 2 * Real.pi * (C₀ + 1) / d ^ 2 := by positivity
  have hkey := key (Real.exp (2 * Real.pi * (C₀ + 1) / d ^ 2)) (Real.one_le_exp (le_of_lt hexp))
  rw [Real.log_exp] at hkey
  rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ d ^ 2 / (2 * Real.pi)),
      ENNReal.ofReal_le_ofReal_iff hC0] at hkey
  have hval : d ^ 2 / (2 * Real.pi) * (2 * Real.pi * (C₀ + 1) / d ^ 2) = C₀ + 1 := by
    field_simp
  linarith [hkey, hval]

end Work.Fatou.Analysis
