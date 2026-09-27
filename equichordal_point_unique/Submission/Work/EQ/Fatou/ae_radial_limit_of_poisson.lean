import Mathlib
import Submission.Work.EQ.FatouDefs
import Submission.Work.EQ.Fatou.pk_mixture
import Submission.Work.EQ.Fatou.pkS_nonneg
import Submission.Work.EQ.Fatou.pkS_mass
import Submission.Work.EQ.Fatou.pkS_tail_tendsto
import Submission.Work.EQ.Fatou.pk_pi_tendsto
import Submission.Work.EQ.Fatou.pk_nonneg
import Submission.Work.EQ.Fatou.integral_pk_eq
import Submission.Work.EQ.Fatou.ae_uniform_interval_average
import Submission.Work.EQ.Fatou.pk_basic
import Submission.Work.EQ.Fatou.cauchy_kernel
import Submission.Work.EQ.Fatou.pk_near_part_bound

set_option maxHeartbeats 1000000

namespace Work.EQ.Fatou

open MeasureTheory Set intervalIntegral Filter

/-- If `discVal g r θ` is the Poisson integral of `F` for every `r ∈ (0,1)`, then subtracting the
value `F θ` turns it into the Poisson integral of `F - F θ`. -/
theorem discVal_sub_eq_integral {g : ℂ → ℂ} {F : ℝ → ℂ}
    (hF : MeasureTheory.LocallyIntegrable F MeasureTheory.volume)
    (hpois : ∀ r ∈ Set.Ioo (0:ℝ) 1, ∀ θ : ℝ,
      Work.EQ.discVal g r θ = (2 * Real.pi)⁻¹ *
        (∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) * F φ))
    {r : ℝ} (hr : r ∈ Set.Ioo (0:ℝ) 1) (θ : ℝ) :
    Work.EQ.discVal g r θ - F θ = (2 * Real.pi)⁻¹ *
      (∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) * (F φ - F θ)) := by
  have hr0 : 0 ≤ r := le_of_lt hr.1
  have hr1 : r < 1 := hr.2
  have hFint : IntervalIntegrable F volume (0:ℝ) (2 * Real.pi) :=
    (hF.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hcont : Continuous (fun φ : ℝ => Work.EQ.pk r (θ - φ)) :=
    (continuous_pk r hr0 hr1).comp (by fun_prop)
  have hcontC : Continuous (fun φ : ℝ => (Work.EQ.pk r (θ - φ) : ℂ)) :=
    Complex.continuous_ofReal.comp hcont
  have hI1 : IntervalIntegrable (fun φ : ℝ => Work.EQ.pk r (θ - φ) * F φ)
      volume (0:ℝ) (2 * Real.pi) :=
    (hFint.mul_continuousOn hcontC.continuousOn).congr (fun x _ => by ring)
  have hI2 : IntervalIntegrable (fun φ : ℝ => Work.EQ.pk r (θ - φ) * F θ)
      volume (0:ℝ) (2 * Real.pi) :=
    (hcontC.intervalIntegrable _ _).mul_const (F θ)
  have hsub : (∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) * (F φ - F θ))
      = (∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) * F φ)
        - (∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) * F θ) := by
    rw [← intervalIntegral.integral_sub hI1 hI2]
    apply intervalIntegral.integral_congr
    intro φ _
    ring
  have hI2val : (∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) * F θ)
      = ((2 * Real.pi : ℝ) : ℂ) * F θ := by
    rw [intervalIntegral.integral_mul_const]
    have hreal : (∫ φ in (0:ℝ)..2 * Real.pi, (Work.EQ.pk r (θ - φ) : ℂ))
        = ((2 * Real.pi : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
      rw [integral_complex_ofReal]
      rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
      rw [integral_pk_shift r θ hr0 hr1]
    rw [hreal]
  have hstep : ↑((2 * Real.pi : ℝ)⁻¹) * (((2 * Real.pi : ℝ) : ℂ) * F θ) = F θ := by
    have hc : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact mul_ne_zero (by norm_num) Real.pi_ne_zero
    rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hkey : (2 * Real.pi)⁻¹ * ((∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) * F φ)
        - ((2 * Real.pi : ℝ) : ℂ) * F θ)
      = (2 * Real.pi)⁻¹ * (∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) * F φ) - F θ := by
    rw [mul_sub, hstep]
  rw [hsub, hI2val, hkey, hpois r hr θ]

/-- **Almost everywhere radial limit of a Poisson integral.**
If the disc values of `g` are the Poisson integrals of the locally integrable boundary function
`F`, then for almost every `θ ∈ (0, 2π)` the disc values converge to `F θ` as the radius tends to
`1` from below. -/
theorem ae_radial_limit_of_poisson {g : ℂ → ℂ} {F : ℝ → ℂ}
    (hF : MeasureTheory.LocallyIntegrable F MeasureTheory.volume)
    (hpois : ∀ r ∈ Set.Ioo (0:ℝ) 1, ∀ θ : ℝ,
      Work.EQ.discVal g r θ = (2 * Real.pi)⁻¹ *
        (∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) * F φ)) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (2 * Real.pi))),
      Filter.Tendsto (fun r : ℝ => Work.EQ.discVal g r θ) (nhdsWithin 1 (Set.Iio 1)) (nhds (F θ)) := by
  have hLeb := ae_uniform_interval_average F hF
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hLeb] with θ hLebθ
  intro hθine
  have hθ0 : 0 < θ := hθine.1
  have hθ2π : θ < 2 * Real.pi := hθine.2
  have hInt : ∀ a b : ℝ, IntervalIntegrable (fun y : ℝ => ‖F y - F θ‖) volume a b := by
    intro a b
    have h1 : IntervalIntegrable (fun y : ℝ => F y - F θ) volume a b :=
      ((hF.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).sub
        (intervalIntegrable_const (μ := volume) (c := F θ))
    exact h1.norm
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hLebθ (ε / 100) (by positivity)
  set δ : ℝ := min (min δ₀ (θ / 2)) (min ((2 * Real.pi - θ) / 2) (Real.pi / 2)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδ₀pos (by linarith)) (lt_min (by linarith) (by positivity))
  have hδle₀ : δ ≤ δ₀ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδθ : δ < θ := by
    rw [hδdef]
    have h1 : min δ₀ (θ / 2) ≤ θ / 2 := min_le_right _ _
    have h2 : min (min δ₀ (θ / 2)) (min ((2 * Real.pi - θ) / 2) (Real.pi / 2))
        ≤ min δ₀ (θ / 2) := min_le_left _ _
    linarith
  have hδ2π : δ < 2 * Real.pi - θ := by
    rw [hδdef]
    have h2 : min (min δ₀ (θ / 2)) (min ((2 * Real.pi - θ) / 2) (Real.pi / 2))
        ≤ min ((2 * Real.pi - θ) / 2) (Real.pi / 2) := min_le_right _ _
    have h3 : min ((2 * Real.pi - θ) / 2) (Real.pi / 2) ≤ (2 * Real.pi - θ) / 2 :=
      min_le_left _ _
    linarith
  have hδπ : δ < Real.pi := by
    rw [hδdef]
    have h2 : min (min δ₀ (θ / 2)) (min ((2 * Real.pi - θ) / 2) (Real.pi / 2))
        ≤ min ((2 * Real.pi - θ) / 2) (Real.pi / 2) := min_le_right _ _
    have h3 : min ((2 * Real.pi - θ) / 2) (Real.pi / 2) ≤ Real.pi / 2 := min_le_right _ _
    linarith
  -- the Lebesgue-point averaging condition in symmetric-interval form
  have havg : ∀ s ∈ Set.Ioc (0:ℝ) δ,
      ∫ φ in (θ - s)..(θ + s), ‖F φ - F θ‖ ≤ 2 * (ε / 100) * s := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hsδ : s ≤ δ := hs.2
    have hsle : s ≤ δ₀ := le_trans hsδ hδle₀
    have hlt := hδ₀ s ⟨hs0, hsle⟩
    have hvol : (MeasureTheory.volume (Set.Icc (θ - s) (θ + s))).toReal = 2 * s := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hvol] at hlt
    have heq : (∫ φ in (θ - s)..(θ + s), ‖F φ - F θ‖)
        = ∫ y in Set.Icc (θ - s) (θ + s), ‖F y - F θ‖ := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact (integral_Icc_eq_integral_Ioc).symm
    have h2s : (0:ℝ) < 2 * s := by linarith
    have hIcc : (∫ y in Set.Icc (θ - s) (θ + s), ‖F y - F θ‖) < 2 * s * (ε / 100) := by
      have hthis := mul_lt_mul_of_pos_left hlt h2s
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h2s), one_mul] at hthis
    rw [heq]
    linarith
  have hnear : ∀ r ∈ Set.Ico (1/2 : ℝ) 1,
      ∫ φ in (θ - δ)..(θ + δ), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖ ≤ 100 * (ε / 100) :=
    pk_near_part_shifted θ δ (ε / 100) hδpos (le_of_lt hδπ) (by positivity)
      (fun φ : ℝ => ‖F φ - F θ‖) (fun φ => norm_nonneg _) (hInt (θ - δ) (θ + δ)) havg
  -- the far part: choose a small uniform bound
  set M : ℝ := ∫ y in (0:ℝ)..(2 * Real.pi), ‖F y - F θ‖ with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact intervalIntegral.integral_nonneg (by positivity) (fun y hy => norm_nonneg _)
  set C : ℝ := ε / (2 * (M + 1)) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCM : C * M ≤ ε / 2 := by
    have hden : 0 < 2 * (M + 1) := by linarith
    rw [hCdef, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [hMnn, hε]
  have hfar : ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1),
      ((1/2 : ℝ) ≤ r ∧ r < 1) ∧ ∀ ψ ∈ Set.Icc δ (2 * Real.pi - δ), Work.EQ.pk r ψ ≤ C := by
    have h01 : ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1), ((1/2 : ℝ) ≤ r ∧ r < 1) := by
      have hlt : ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1), r < 1 := self_mem_nhdsWithin
      have hgt : ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1), (1/2 : ℝ) < r := by
        filter_upwards [nhdsWithin_le_nhds
          (Ioi_mem_nhds (show (1/2 : ℝ) < 1 by norm_num))] with r hr
        exact hr
      filter_upwards [hlt, hgt] with r h1 h2
      exact ⟨le_of_lt h2, h1⟩
    filter_upwards [h01, pk_far_bound δ C hδpos hδπ hCpos] with r hr hb
    exact ⟨hr, hb⟩
  filter_upwards [hfar] with r hr
  obtain ⟨⟨hr12, hr1⟩, hbound⟩ := hr
  have hr0 : 0 < r := by linarith
  have hmix : r ∈ Set.Ioo (0:ℝ) 1 := ⟨hr0, hr1⟩
  have hsub := discVal_sub_eq_integral hF hpois hmix θ
  have hpkcont : Continuous (fun φ : ℝ => Work.EQ.pk r (θ - φ)) :=
    (continuous_pk r hr0.le hr1).comp (by fun_prop)
  have hint : IntervalIntegrable (fun φ : ℝ => Work.EQ.pk r (θ - φ) * (F φ - F θ))
      volume (0:ℝ) (2 * Real.pi) := by
    have hFint : IntervalIntegrable (fun φ : ℝ => F φ - F θ) volume (0:ℝ) (2 * Real.pi) :=
      ((hF.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).sub
        (intervalIntegrable_const (μ := volume) (c := F θ))
    have hcontC : Continuous (fun φ : ℝ => (Work.EQ.pk r (θ - φ) : ℂ)) :=
      Complex.continuous_ofReal.comp hpkcont
    exact (hFint.mul_continuousOn hcontC.continuousOn).congr (fun x _ => by ring)
  have hstep1 : ‖∫ φ in (0:ℝ)..(2 * Real.pi), Work.EQ.pk r (θ - φ) * (F φ - F θ)‖
      ≤ ∫ φ in (0:ℝ)..(2 * Real.pi), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖ := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by positivity)) ?_
    have h1 : IntervalIntegrable (fun φ : ℝ => ‖Work.EQ.pk r (θ - φ) * (F φ - F θ)‖)
        volume (0:ℝ) (2 * Real.pi) := hint.norm
    have h2 : IntervalIntegrable (fun φ : ℝ => Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
        volume (0:ℝ) (2 * Real.pi) :=
      ((hInt 0 (2 * Real.pi)).mul_continuousOn hpkcont.continuousOn).congr
        (fun x _ => by ring)
    refine integral_mono_on (by positivity) h1 h2 (fun φ hφ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pk_nonneg r (θ - φ) hr0.le hr1)]
  have hI0 : IntervalIntegrable (fun φ : ℝ => Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
      volume (0:ℝ) (θ - δ) :=
    ((hInt 0 (θ - δ)).mul_continuousOn hpkcont.continuousOn).congr (fun x _ => by ring)
  have hI1 : IntervalIntegrable (fun φ : ℝ => Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
      volume (θ - δ) (θ + δ) :=
    ((hInt (θ - δ) (θ + δ)).mul_continuousOn hpkcont.continuousOn).congr (fun x _ => by ring)
  have hI2 : IntervalIntegrable (fun φ : ℝ => Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
      volume (θ + δ) (2 * Real.pi) :=
    ((hInt (θ + δ) (2 * Real.pi)).mul_continuousOn hpkcont.continuousOn).congr
      (fun x _ => by ring)
  have hfar_bound : (∫ φ in (0:ℝ)..(θ - δ), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
      + (∫ φ in (θ + δ)..(2 * Real.pi), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖) ≤ C * M :=
    pk_far_piece_le r C θ δ hr0.le hr1 (le_of_lt hCpos) hδpos hδθ hθ2π hδ2π
      (fun y : ℝ => ‖F y - F θ‖) (fun y => norm_nonneg _) (hInt 0 (2 * Real.pi)) hbound
  have hnear_bound := hnear r ⟨hr12, hr1⟩
  have hsplitA : (∫ φ in (0:ℝ)..(2 * Real.pi), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
      = (∫ φ in (0:ℝ)..(θ - δ), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
        + (∫ φ in (θ - δ)..(2 * Real.pi), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖) :=
    (intervalIntegral.integral_add_adjacent_intervals hI0 (hI1.trans hI2)).symm
  have hsplitB : (∫ φ in (θ - δ)..(2 * Real.pi), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
      = (∫ φ in (θ - δ)..(θ + δ), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
        + (∫ φ in (θ + δ)..(2 * Real.pi), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖) :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  have hsum : (∫ φ in (0:ℝ)..(2 * Real.pi), Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
      ≤ C * M + 100 * (ε / 100) := by
    rw [hsplitA, hsplitB]
    have hh := add_le_add hfar_bound hnear_bound
    linarith [hh]
  rw [dist_eq_norm, hsub, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (2 * Real.pi)⁻¹)]
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  have h5 : (2 * Real.pi)⁻¹ * (3/2 * ε) < ε := by
    rw [inv_mul_eq_div, div_lt_iff₀ h2π]
    nlinarith [hε, Real.pi_gt_three]
  have hbound2 : C * M + 100 * (ε / 100) ≤ 3/2 * ε := by linarith [hCM]
  have hmono : (2 * Real.pi)⁻¹ * (∫ φ in (0:ℝ)..(2 * Real.pi),
        Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖)
      ≤ (2 * Real.pi)⁻¹ * (C * M + 100 * (ε / 100)) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hfinal : (2 * Real.pi)⁻¹ * (∫ φ in (0:ℝ)..(2 * Real.pi),
        Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖) < ε := by
    have hmid := mul_le_mul_of_nonneg_left hbound2 (by positivity : (0:ℝ) ≤ (2 * Real.pi)⁻¹)
    linarith [hmono, hmid, h5]
  calc (2 * Real.pi)⁻¹ * ‖∫ φ in (0:ℝ)..(2 * Real.pi),
          Work.EQ.pk r (θ - φ) * (F φ - F θ)‖
      ≤ (2 * Real.pi)⁻¹ * ∫ φ in (0:ℝ)..(2 * Real.pi),
          Work.EQ.pk r (θ - φ) * ‖F φ - F θ‖ :=
        mul_le_mul_of_nonneg_left hstep1 (by positivity)
    _ < ε := hfinal

end Work.EQ.Fatou
