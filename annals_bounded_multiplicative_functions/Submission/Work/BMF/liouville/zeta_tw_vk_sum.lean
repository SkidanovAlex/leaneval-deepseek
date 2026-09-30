import Mathlib
import Submission.Work.BMF.VKdenom
import Submission.Work.BMF.liouville.zeta_tw_perron

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open MeasureTheory intervalIntegral
open scoped Real Interval Topology

noncomputable section

/-- Pointwise bound for the twisted Perron integrand, given a bound for `ζ′/ζ` at the
corresponding point. -/
lemma norm_zetaTwG_le {u x B : ℝ} (hx : 0 < x) {w : ℂ} (hw : w ≠ 0)
    (hB : ‖deriv riemannZeta (w + (u : ℂ) * Complex.I) /
        riemannZeta (w + (u : ℂ) * Complex.I)‖ ≤ B) :
    ‖zetaTwG u x w‖ ≤ B * (x ^ w.re / ‖w‖) := by
  have h1 : ‖(x : ℂ) ^ w‖ = x ^ w.re := Complex.norm_cpow_eq_rpow_re_of_pos hx w
  have h2 : 0 ≤ x ^ w.re / ‖w‖ :=
    div_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)
  have h3 : ‖-deriv riemannZeta (w + (u : ℂ) * Complex.I) /
      riemannZeta (w + (u : ℂ) * Complex.I)‖ ≤ B := by simpa using hB
  rw [zetaTwG, norm_div, norm_mul, h1]
  calc ‖-deriv riemannZeta (w + (u : ℂ) * Complex.I) /
        riemannZeta (w + (u : ℂ) * Complex.I)‖ * x ^ w.re / ‖w‖
      = ‖-deriv riemannZeta (w + (u : ℂ) * Complex.I) /
        riemannZeta (w + (u : ℂ) * Complex.I)‖ * (x ^ w.re / ‖w‖) := by ring
    _ ≤ B * (x ^ w.re / ‖w‖) := mul_le_mul_of_nonneg_right h3 h2

/-- Norm of the vertical contour point `σ₁ + i t`. -/
lemma norm_sigma_add_I_mul (σ₁ t : ℝ) :
    ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖ = Real.sqrt (σ₁ ^ 2 + t ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  ring

/-- `√(σ²+t²) ≥ (σ+|t|)/√2`. -/
lemma norm_sigma_add_I_mul_ge (σ₁ t : ℝ) (hσ : 0 < σ₁) :
    (σ₁ + |t|) / Real.sqrt 2 ≤ ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖ := by
  rw [norm_sigma_add_I_mul]
  rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2))]
  rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ σ₁ ^ 2 + t ^ 2) 2]
  calc σ₁ + |t| = Real.sqrt ((σ₁ + |t|) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt ((σ₁ ^ 2 + t ^ 2) * 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (σ₁ - |t|), abs_nonneg t, sq_abs t])

/-- `∫_{-T}^{T} dt/(σ+|t|) = 2 log(1 + T/σ)` for `σ > 0`, `T ≥ 0`. -/
lemma integral_inv_sigma_abs (σ₁ T : ℝ) (hσ₁ : 0 < σ₁) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, 1 / (σ₁ + |t|) = 2 * Real.log (1 + T / σ₁) := by
  have hcont : ContinuousOn (fun t : ℝ => 1 / (σ₁ + |t|)) (Set.Icc (-T) T) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_const.add continuous_abs.continuousOn
    · intro t ht
      exact ne_of_gt (add_pos_of_pos_of_nonneg hσ₁ (abs_nonneg t))
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 / (σ₁ + |t|)) volume (-T) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : -T ≤ (0:ℝ))]
    exact hcont.mono (Set.Icc_subset_Icc le_rfl hT)
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / (σ₁ + |t|)) volume (0:ℝ) T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact hcont.mono (Set.Icc_subset_Icc (by linarith) le_rfl)
  have hsymm : ∫ x in (-T)..0, 1 / (σ₁ + |x|) = ∫ x in (0:ℝ)..T, 1 / (σ₁ + |x|) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => 1 / (σ₁ + |x|)) (a := (0:ℝ)) (b := T)
    simp only [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [abs_neg]
  have hFTC : ∫ t in (0:ℝ)..T, 1 / (σ₁ + t) = Real.log (σ₁ + T) - Real.log σ₁ := by
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) T,
        HasDerivAt (fun t : ℝ => Real.log (σ₁ + t)) (1 / (σ₁ + x)) x := by
      intro x hx
      have hx0 : (0:ℝ) ≤ x := by
        rw [Set.uIcc_of_le hT] at hx
        exact hx.1
      have hpos : σ₁ + x ≠ 0 := by linarith
      have h1 : HasDerivAt (fun t : ℝ => σ₁ + t) 1 x := (hasDerivAt_id x).const_add σ₁
      have h2 := h1.log hpos
      convert h2 using 1
    have hint : IntervalIntegrable (fun t : ℝ => 1 / (σ₁ + t)) volume (0:ℝ) T := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hT]
      refine ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id) ?_
      intro t ht
      have : (0:ℝ) ≤ t := ht.1
      linarith
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simpa using h
  have hcongr : ∫ t in (0:ℝ)..T, 1 / (σ₁ + |t|) = ∫ t in (0:ℝ)..T, 1 / (σ₁ + t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    show 1 / (σ₁ + |t|) = 1 / (σ₁ + t)
    rw [abs_of_nonneg ht.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, hsymm, hcongr, hFTC]
  have hpos : 0 < σ₁ + T := by linarith
  rw [← Real.log_div hpos.ne' (ne_of_gt hσ₁)]
  congr 1
  field_simp
  ring

/-- Bound for the left edge of the twisted Perron rectangle. -/
lemma norm_zetaTwLeft_le {u x T σ₁ B : ℝ} (hx : 1 < x) (hT : 0 < T) (hσ₁ : 0 < σ₁)
    (hB : 0 ≤ B)
    (hD : ∀ t : ℝ, |t| ≤ T → ‖deriv riemannZeta
        ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I)‖
        ≤ B * (Real.log (|t + u| + 3)) ^ 2) :
    ‖zetaTwLeft u x T σ₁‖ ≤
      B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) := by
  have hx0 : 0 < x := by linarith
  have hloguT0 : 0 < Real.log (|u| + T + 3) := by
    apply Real.log_pos
    have := abs_nonneg u
    linarith
  have hpt : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (-T) T →
      ‖zetaTwG u x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * (Real.sqrt 2 / (σ₁ + |t|)) := by
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.mem_Ioc] at ht
    have htabs : |t| ≤ T := by
      rw [abs_le]
      exact ⟨by linarith [ht.1], ht.2⟩
    have hw : ((σ₁ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have h1 : ((σ₁ : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h0]; simp
      simp at h1
      linarith
    have harg : (σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I
        = ((σ₁ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ) * Complex.I := by
      push_cast
      ring
    have hD' := hD t htabs
    rw [harg] at hD'
    have h1 := norm_zetaTwG_le (u := u) (B := B * (Real.log (|t + u| + 3)) ^ 2) hx0 hw hD'
    have h2 : Real.log (|t + u| + 3) ≤ Real.log (|u| + T + 3) := by
      apply Real.log_le_log (by positivity)
      have h3 : |t + u| ≤ |t| + |u| := abs_add_le t u
      linarith
    have h3 : 0 ≤ Real.log (|t + u| + 3) := by
      apply Real.log_nonneg
      have := abs_nonneg (t + u)
      linarith
    have h4 : (Real.log (|t + u| + 3)) ^ 2 ≤ (Real.log (|u| + T + 3)) ^ 2 := by
      have h5 : |Real.log (|t + u| + 3)| ≤ Real.log (|u| + T + 3) := by
        rw [abs_of_nonneg h3]
        exact h2
      rw [← sq_abs (Real.log (|t + u| + 3))]
      exact pow_le_pow_left₀ (abs_nonneg _) h5 2
    rw [show ((σ₁ : ℂ) + (t : ℂ) * Complex.I).re = σ₁ by simp] at h1
    have h7 : (σ₁ + |t|) / Real.sqrt 2 ≤ ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖ :=
      norm_sigma_add_I_mul_ge σ₁ t hσ₁
    have h9 : (0:ℝ) < σ₁ + |t| := add_pos_of_pos_of_nonneg hσ₁ (abs_nonneg t)
    have h10 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
    have hwpos : (0:ℝ) < ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖ := norm_pos_iff.mpr hw
    have hxs : (0:ℝ) < x ^ σ₁ := Real.rpow_pos_of_pos hx0 σ₁
    have hkey : 1 / ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖ ≤ Real.sqrt 2 / (σ₁ + |t|) := by
      rw [div_le_div_iff₀ hwpos h9]
      have hh := mul_le_mul_of_nonneg_right h7 h10.le
      rw [div_mul_cancel₀ _ (ne_of_gt h10)] at hh
      linarith
    have h8 : x ^ σ₁ / ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖
        ≤ x ^ σ₁ * (Real.sqrt 2 / (σ₁ + |t|)) := by
      calc x ^ σ₁ / ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖
          = x ^ σ₁ * (1 / ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖) := by ring
        _ ≤ x ^ σ₁ * (Real.sqrt 2 / (σ₁ + |t|)) := mul_le_mul_of_nonneg_left hkey hxs.le
    have h11 : B * (Real.log (|t + u| + 3)) ^ 2 ≤ B * (Real.log (|u| + T + 3)) ^ 2 :=
      mul_le_mul_of_nonneg_left h4 hB
    have h12 : 0 ≤ x ^ σ₁ / ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖ := by
      exact div_nonneg hxs.le (norm_nonneg _)
    calc ‖zetaTwG u x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ B * (Real.log (|t + u| + 3)) ^ 2 *
            (x ^ σ₁ / ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖) := h1
      _ ≤ B * (Real.log (|u| + T + 3)) ^ 2 *
            (x ^ σ₁ / ‖(σ₁ : ℂ) + (t : ℂ) * Complex.I‖) :=
          mul_le_mul_of_nonneg_right h11 h12
      _ ≤ B * (Real.log (|u| + T + 3)) ^ 2 * (x ^ σ₁ * (Real.sqrt 2 / (σ₁ + |t|))) :=
          mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * (Real.sqrt 2 / (σ₁ + |t|)) := by ring
  have hcont : ContinuousOn
      (fun t : ℝ => B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * (Real.sqrt 2 / (σ₁ + |t|)))
      (Set.Icc (-T) T) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_const.add continuous_abs.continuousOn
    · intro t ht
      exact ne_of_gt (add_pos_of_pos_of_nonneg hσ₁ (abs_nonneg t))
  have hint : IntervalIntegrable
      (fun t : ℝ => B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * (Real.sqrt 2 / (σ₁ + |t|)))
      volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact hcont
  have hnorm : ‖∫ t in (-T)..T, zetaTwG u x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ∫ t in (-T)..T, B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ *
          (Real.sqrt 2 / (σ₁ + |t|)) :=
    intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T) hpt hint
  have hval : ∫ t in (-T)..T, B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ *
      (Real.sqrt 2 / (σ₁ + |t|))
      = B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) := by
    rw [show (fun t : ℝ => B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * (Real.sqrt 2 / (σ₁ + |t|)))
        = fun t : ℝ => (B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * Real.sqrt 2) *
            (1 / (σ₁ + |t|)) by
      ext t; ring]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_inv_sigma_abs σ₁ T hσ₁ hT.le]
    ring
  rw [hval] at hnorm
  have hle1 : (1:ℝ) / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hnn : 0 ≤ B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ *
      (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) := by
    have hlt : 0 < Real.log (1 + T / σ₁) := by
      apply Real.log_pos
      rw [lt_add_iff_pos_right, div_pos_iff]
      exact Or.inl ⟨hT, hσ₁⟩
    have hxs : 0 < x ^ σ₁ := Real.rpow_pos_of_pos hx0 σ₁
    have hlog2 : 0 < Real.log (|u| + T + 3) := hloguT0
    positivity
  have hfin : (1 / (2 * Real.pi)) *
      (B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)))
      ≤ B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ *
        (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) := by
    calc (1 / (2 * Real.pi)) *
          (B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)))
        ≤ 1 * (B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ *
            (2 * Real.sqrt 2 * Real.log (1 + T / σ₁))) :=
          mul_le_mul_of_nonneg_right hle1 hnn
      _ = B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ * (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) := by
          rw [one_mul]
  rw [zetaTwLeft, norm_mul]
  have hπnorm : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hπnorm]
  calc (1 / (2 * Real.pi)) *
        ‖∫ t in (-T)..T, zetaTwG u x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (1 / (2 * Real.pi)) *
        (B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ *
          (2 * Real.sqrt 2 * Real.log (1 + T / σ₁))) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ B * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ *
        (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) := hfin


/-- Bound for a horizontal edge (`Im w = r`, `|r| = T`) of the twisted Perron rectangle. -/
lemma norm_horiz_edge_le {u x T σ₁ B r : ℝ} (hx : 1 < x) (hσ₁ : 0 < σ₁) (hT : 0 < T)
    (hσ₁σ₀ : σ₁ ≤ 1 + 1 / Real.log x) (hB : 0 ≤ B) (hr : |r| = T)
    (hD : ∀ v : ℝ, σ₁ ≤ v → v ≤ 1 + 1 / Real.log x →
      ‖deriv riemannZeta ((v : ℂ) + ((r + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((v : ℂ) + ((r + u : ℝ) : ℂ) * Complex.I)‖
        ≤ B * (Real.log (|r + u| + 3)) ^ 2) :
    ‖(1 / (2 * Real.pi * Complex.I)) *
        ∫ v in σ₁..(1 + 1 / Real.log x), zetaTwG u x ((v : ℂ) + (r : ℂ) * Complex.I)‖
      ≤ B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) *
          ((1 + 1 / Real.log x) - σ₁) / T := by
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hloguT : 0 ≤ Real.log (|u| + T + 3) := by
    apply Real.log_nonneg
    have := abs_nonneg u
    linarith
  have hpt : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Set.Ioc σ₁ (1 + 1 / Real.log x) →
      ‖zetaTwG u x ((v : ℂ) + (r : ℂ) * Complex.I)‖
        ≤ B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) / T := by
    apply Filter.Eventually.of_forall
    intro v hv
    rw [Set.mem_Ioc] at hv
    have hvσ₀ : v ≤ 1 + 1 / Real.log x := hv.2
    have hw : ((v : ℂ) + (r : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have h1 : ((v : ℂ) + (r : ℂ) * Complex.I).im = 0 := by rw [h0]; simp
      have h2 : r = 0 := by simpa using h1
      have h3 : T = 0 := by rw [← hr, h2]; simp
      linarith
    have harg : (v : ℂ) + ((r + u : ℝ) : ℂ) * Complex.I
        = ((v : ℂ) + (r : ℂ) * Complex.I) + (u : ℂ) * Complex.I := by
      push_cast
      ring
    have hD' := hD v (le_of_lt hv.1) hvσ₀
    rw [harg] at hD'
    have h1 := norm_zetaTwG_le (u := u) (B := B * (Real.log (|r + u| + 3)) ^ 2) hx0 hw hD'
    have h2 : Real.log (|r + u| + 3) ≤ Real.log (|u| + T + 3) := by
      apply Real.log_le_log (by positivity)
      have h3 : |r + u| ≤ |r| + |u| := abs_add_le r u
      rw [hr] at h3
      linarith
    have h3 : 0 ≤ Real.log (|r + u| + 3) := by
      apply Real.log_nonneg
      have := abs_nonneg (r + u)
      linarith
    have h4 : (Real.log (|r + u| + 3)) ^ 2 ≤ (Real.log (|u| + T + 3)) ^ 2 := by
      have h5 : |Real.log (|r + u| + 3)| ≤ Real.log (|u| + T + 3) := by
        rw [abs_of_nonneg h3]
        exact h2
      rw [← sq_abs (Real.log (|r + u| + 3))]
      exact pow_le_pow_left₀ (abs_nonneg _) h5 2
    rw [show ((v : ℂ) + (r : ℂ) * Complex.I).re = v by simp] at h1
    have hnorm : T ≤ ‖(v : ℂ) + (r : ℂ) * Complex.I‖ := by
      have h6 := Complex.abs_im_le_norm ((v : ℂ) + (r : ℂ) * Complex.I)
      have h7 : ((v : ℂ) + (r : ℂ) * Complex.I).im = r := by simp
      rw [h7, hr] at h6
      exact h6
    have hxpow : x ^ v ≤ x ^ (1 + 1 / Real.log x) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hx) hvσ₀
    have hxpos : 0 < x ^ v := Real.rpow_pos_of_pos hx0 v
    have hupper : x ^ v / ‖(v : ℂ) + (r : ℂ) * Complex.I‖
        ≤ x ^ (1 + 1 / Real.log x) / T := by
      have hwpos : 0 < ‖(v : ℂ) + (r : ℂ) * Complex.I‖ := lt_of_lt_of_le hT hnorm
      rw [div_le_div_iff₀ hwpos hT]
      exact mul_le_mul hxpow hnorm hT.le (Real.rpow_nonneg hx0.le _)
    have h11 : B * (Real.log (|r + u| + 3)) ^ 2 ≤ B * (Real.log (|u| + T + 3)) ^ 2 :=
      mul_le_mul_of_nonneg_left h4 hB
    have h12 : 0 ≤ x ^ v / ‖(v : ℂ) + (r : ℂ) * Complex.I‖ :=
      div_nonneg hxpos.le (norm_nonneg _)
    calc ‖zetaTwG u x ((v : ℂ) + (r : ℂ) * Complex.I)‖
        ≤ B * (Real.log (|r + u| + 3)) ^ 2 *
            (x ^ v / ‖(v : ℂ) + (r : ℂ) * Complex.I‖) := h1
      _ ≤ B * (Real.log (|u| + T + 3)) ^ 2 *
            (x ^ v / ‖(v : ℂ) + (r : ℂ) * Complex.I‖) :=
          mul_le_mul_of_nonneg_right h11 h12
      _ ≤ B * (Real.log (|u| + T + 3)) ^ 2 * (x ^ (1 + 1 / Real.log x) / T) :=
          mul_le_mul_of_nonneg_left hupper (mul_nonneg hB (sq_nonneg _))
      _ = B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) / T := by ring
  have hcont : ContinuousOn
      (fun v : ℝ => B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) / T)
      (Set.Icc σ₁ (1 + 1 / Real.log x)) := continuousOn_const
  have hint : IntervalIntegrable
      (fun v : ℝ => B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) / T)
      volume σ₁ (1 + 1 / Real.log x) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ₁σ₀]
    exact hcont
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hσ₁σ₀ hpt hint
  have hval : ∫ v in σ₁..(1 + 1 / Real.log x),
        B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) / T
      = (B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) / T) *
          ((1 + 1 / Real.log x) - σ₁) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hval] at hnorm
  rw [norm_mul]
  have hπnorm : ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ ≤ 1 / (2 * Real.pi) := by
    rw [norm_div, norm_mul]
    have h2 : ‖(2 : ℂ) * ((Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
      have : (2 : ℂ) * ((Real.pi : ℝ) : ℂ) = (((2 : ℝ) * Real.pi : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [norm_one, h2, Complex.norm_I, mul_one]
  calc ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ *
        ‖∫ v in σ₁..(1 + 1 / Real.log x), zetaTwG u x ((v : ℂ) + (r : ℂ) * Complex.I)‖
      ≤ (1 / (2 * Real.pi)) *
        ((B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) / T) *
          ((1 + 1 / Real.log x) - σ₁)) :=
        mul_le_mul hπnorm hnorm (norm_nonneg _) (by positivity)
    _ ≤ B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) *
          ((1 + 1 / Real.log x) - σ₁) / T := by
        have hπ : (0:ℝ) < 2 * Real.pi := by positivity
        have hle : 1 / (2 * Real.pi) ≤ 1 := by
          rw [div_le_one hπ]
          nlinarith [Real.pi_gt_three]
        have hnn : 0 ≤ (B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) / T) *
            ((1 + 1 / Real.log x) - σ₁) := by
          apply mul_nonneg
          · apply div_nonneg _ hT.le
            positivity
          · linarith
        calc (1 / (2 * Real.pi)) *
              ((B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) / T) *
                ((1 + 1 / Real.log x) - σ₁))
            ≤ 1 * ((B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) / T) *
                ((1 + 1 / Real.log x) - σ₁)) :=
              mul_le_mul_of_nonneg_right hle hnn
          _ = B * (Real.log (|u| + T + 3)) ^ 2 * x ^ (1 + 1 / Real.log x) *
                ((1 + 1 / Real.log x) - σ₁) / T := by ring

end

end Work.BMF.liouville
