import Mathlib
import Submission.Work.Pert.pert2v2.Xc_segment_log_bound
import Submission.Work.Pert.pert2v2.rig_of_coher_segment
import Submission.Work.Pert.limitCoord_plus_exists
import Submission.Work.Pert.pert2v2.Psi_Xc_constant_v2
import Submission.Work.Pert.waist_cover_pinned_v2

/-!
# `Work.Pert.pert2v2.LeadWire.SegSetup` — the single-height segment of the (A.4.4) row

The datum-level choice of the height `y₀` of the (A.4.4) segment and the compact
`Kp = Xc d '' {x + i y₀ | x ∈ [0,1]}` on which the crux (`crux_limit_v8`) pins its upper-gate
coordinate.  Everything here depends only on the datum `d`, the gate parameter `Ξ'` and a lower
bound `Yx` supplied by the caller.
-/

namespace Work.Pert.pert2v2.LeadWire

open _root_.MandelDim Complex Set Metric

/-- `Xc_segment_log_bound` on the CLOSED segment `x ∈ [0,1]`. -/
theorem Xc_segment_log_bound_Icc {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ A C Y : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ y₀ : ℝ, Y ≤ y₀ → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)
        - ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ ≤ A * Real.log (y₀ + 2) + C := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨R, hR⟩ := hasym 1 one_pos
  refine ⟨‖a‖, 1 + ‖a‖ * Real.pi + ‖b‖, max (R + 1) (max (2 * (1 + d.ξ₀) + 1) 1),
    norm_nonneg a, ?_, ?_⟩
  · have ha := norm_nonneg a
    have hb := norm_nonneg b
    have hp : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    have hmul : 0 ≤ ‖a‖ * Real.pi := mul_nonneg ha hp
    linarith
  intro y₀ hy x hx
  obtain ⟨hx0, hx1⟩ := hx
  have hY : max (R + 1) (max (2 * (1 + d.ξ₀) + 1) 1) ≤ y₀ := hy
  have h1 : R + 1 ≤ y₀ := le_trans (le_max_left _ _) hY
  have h2 : max (2 * (1 + d.ξ₀) + 1) 1 ≤ y₀ := le_trans (le_max_right _ _) hY
  have hy1 : (1 : ℝ) ≤ y₀ := le_trans (le_max_right _ _) h2
  have hyξ : 2 * (1 + d.ξ₀) + 1 ≤ y₀ := le_trans (le_max_left _ _) h2
  have hyR : R < y₀ := by linarith
  have hy0 : 0 < y₀ := lt_of_lt_of_le zero_lt_one hy1
  set w : ℂ := (x : ℂ) + (y₀ : ℂ) * Complex.I with hwdef
  have hwre : w.re = x := by rw [hwdef]; simp
  have hwim : w.im = y₀ := by rw [hwdef]; simp
  have hwnorm_ge : y₀ ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    rw [hwim, abs_of_pos hy0] at h
    exact h
  have hwnorm_le : ‖w‖ ≤ y₀ + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [hwre, hwim, abs_of_nonneg hx0, abs_of_pos hy0] at h
    linarith
  have hwnorm_pos : 0 < ‖w‖ := lt_of_lt_of_le hy0 hwnorm_ge
  have hQ : w ∈ MandelDim.QLeft d.ξ₀ := by
    rw [Work.Parab.QLeft_iff]
    have hre : (w + (d.ξ₀ : ℂ)).re = x + d.ξ₀ := by
      rw [Complex.add_re, Complex.ofReal_re, hwre]
    have him : (w + (d.ξ₀ : ℂ)).im = y₀ := by
      rw [Complex.add_im, Complex.ofReal_im, hwim]
      ring
    rw [hre]
    calc 2 * (x + d.ξ₀) < 2 * (1 + d.ξ₀) + 1 := by linarith
      _ ≤ y₀ := hyξ
      _ = |(w + (d.ξ₀ : ℂ)).im| := by rw [him, abs_of_pos hy0]
      _ ≤ ‖w + (d.ξ₀ : ℂ)‖ := Complex.abs_im_le_norm _
  have hasymw : ‖MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b)‖ < 1 :=
    hR w hQ (lt_of_lt_of_le hyR hwnorm_ge)
  have hlogbound : ‖Complex.log (-w)‖ ≤ Real.log (y₀ + 2) + Real.pi := by
    have h1 := Work.Pert.pert2v2.norm_log_le_abs_log_norm_add_pi (-w)
    have h2 : |Real.log ‖-w‖| ≤ Real.log (y₀ + 2) := by
      rw [norm_neg, abs_of_nonneg (Real.log_nonneg (le_trans hy1 hwnorm_ge))]
      exact Real.log_le_log hwnorm_pos hwnorm_le
    linarith
  have heq : Work.Pert.Xc d w - w
      = (MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b))
        + (a * Complex.log (-w) + b) := by
    simp only [Work.Pert.Xc]
    ring
  rw [heq]
  calc ‖(MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b))
          + (a * Complex.log (-w) + b)‖
      ≤ ‖MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b)‖
          + ‖a * Complex.log (-w) + b‖ := norm_add_le _ _
    _ ≤ 1 + (‖a‖ * ‖Complex.log (-w)‖ + ‖b‖) := by
        have h2 : ‖a * Complex.log (-w) + b‖ ≤ ‖a‖ * ‖Complex.log (-w)‖ + ‖b‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
        linarith
    _ ≤ 1 + (‖a‖ * (Real.log (y₀ + 2) + Real.pi) + ‖b‖) := by
        have h3 := mul_le_mul_of_nonneg_left hlogbound (norm_nonneg a)
        linarith
    _ = ‖a‖ * Real.log (y₀ + 2) + (1 + ‖a‖ * Real.pi + ‖b‖) := by ring

/-- Coordinates of a point in the closed disc of radius `r` about `y₀ i`. -/
theorem re_im_of_near_axis {z : ℂ} {y₀ r : ℝ} (h : ‖z - (y₀ : ℂ) * Complex.I‖ ≤ r) :
    |z.re| ≤ r ∧ |z.im - y₀| ≤ r := by
  have h1 := Complex.abs_re_le_norm (z - (y₀ : ℂ) * Complex.I)
  have h2 := Complex.abs_im_le_norm (z - (y₀ : ℂ) * Complex.I)
  have hre : (z - (y₀ : ℂ) * Complex.I).re = z.re := by simp
  have him : (z - (y₀ : ℂ) * Complex.I).im = z.im - y₀ := by simp
  rw [hre] at h1
  rw [him] at h2
  exact ⟨le_trans h1 h, le_trans h2 h⟩

/-- **The datum-level segment.** -/
theorem seg_setup {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ξ' : ℝ} (hΞ' : 0 < Ξ') (Yx : ℝ) :
    ∃ y₀ : ℝ, Yx ≤ y₀ ∧ 4 * Ξ' + 32 ≤ y₀ ∧ d.η₀ < y₀ ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I) - (y₀ : ℂ) * Complex.I‖ ≤ y₀ / 16) ∧
      IsCompact ((fun x : ℝ => Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
        '' Set.Icc (0 : ℝ) 1) ∧
      (∀ ζ ∈ (fun x : ℝ => Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
          '' Set.Icc (0 : ℝ) 1, MandelDim.tau0 ζ ∈ MandelDim.ParabolicBasin f₀ D₀) ∧
      (fun x : ℝ => Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)) '' Set.Icc (0 : ℝ) 1
        ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none ∧
      IsCompact ((fun x : ℝ => (x : ℂ) + (y₀ : ℂ) * Complex.I) '' Set.Icc (0 : ℝ) 1) ∧
      (fun x : ℝ => (x : ℂ) + (y₀ : ℂ) * Complex.I) '' Set.Icc (0 : ℝ) 1 ⊆ d.DE := by
  obtain ⟨A, C, Y, hA, hC, hlog⟩ := Xc_segment_log_bound_Icc d
  obtain ⟨Yb, hYb0, hYb⟩ := Work.Pert.exists_add_mul_log_lt_half (A / 4) (8 * (C + 2))
    (by positivity)
  set y₀ : ℝ := max (max Yx (4 * Ξ' + 32)) (max (max (|d.η₀| + 1) (2 * (1 + d.ξ₀) + 1))
    (max Y Yb)) with hy₀def
  have hA1 : max Yx (4 * Ξ' + 32) ≤ y₀ := le_max_left _ _
  have hA2 : max (max (|d.η₀| + 1) (2 * (1 + d.ξ₀) + 1)) (max Y Yb) ≤ y₀ := le_max_right _ _
  have hYx : Yx ≤ y₀ := le_trans (le_max_left _ _) hA1
  have hΞy : 4 * Ξ' + 32 ≤ y₀ := le_trans (le_max_right _ _) hA1
  have hA3 : max (|d.η₀| + 1) (2 * (1 + d.ξ₀) + 1) ≤ y₀ := le_trans (le_max_left _ _) hA2
  have hA4 : max Y Yb ≤ y₀ := le_trans (le_max_right _ _) hA2
  have hη : |d.η₀| + 1 ≤ y₀ := le_trans (le_max_left _ _) hA3
  have hξ : 2 * (1 + d.ξ₀) + 1 ≤ y₀ := le_trans (le_max_right _ _) hA3
  have hY : Y ≤ y₀ := le_trans (le_max_left _ _) hA4
  have hYb' : Yb ≤ y₀ := le_trans (le_max_right _ _) hA4
  have hy₀pos : 0 < y₀ := by linarith
  have hη' : d.η₀ < y₀ := by linarith [le_abs_self d.η₀]
  -- the deviation of the curve on the closed segment
  have hdevZ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I) - (y₀ : ℂ) * Complex.I‖ ≤ y₀ / 16 := by
    intro x hx
    have h1 := hlog y₀ hY x hx
    have h2 := hYb y₀ hYb'
    have hlog0 : 0 ≤ Real.log (y₀ + 2) := Real.log_nonneg (by linarith)
    have hx' : ‖((x : ℂ) + (y₀ : ℂ) * Complex.I) - (y₀ : ℂ) * Complex.I‖ ≤ 1 := by
      have : ((x : ℂ) + (y₀ : ℂ) * Complex.I) - (y₀ : ℂ) * Complex.I = (x : ℂ) := by ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    have htri : ‖Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I) - (y₀ : ℂ) * Complex.I‖
        ≤ ‖Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I) - ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖
          + ‖((x : ℂ) + (y₀ : ℂ) * Complex.I) - (y₀ : ℂ) * Complex.I‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h3 : A * Real.log (y₀ + 2) + C + 1 ≤ y₀ / 16 := by
      have : 8 * (C + 2) + 32 * (A / 4) * Real.log (y₀ + 2) < y₀ / 2 := h2
      nlinarith
    linarith
  -- the curve point in the left cone (for compactness)
  have hseg : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
    intro x hx0 hx1
    rw [Work.Pert.pert2v2.mem_Qreg_left_iff]
    obtain ⟨hre, him⟩ := re_im_of_near_axis (hdevZ x ⟨hx0, hx1⟩)
    have hre' := (abs_le.mp hre).2
    have him' := (abs_le.mp him).1
    have hpos : 0 ≤ (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)).im := by linarith
    rw [abs_of_nonneg hpos]
    linarith
  have hKpc : IsCompact ((fun x : ℝ => Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
      '' Set.Icc (0 : ℝ) 1) :=
    Work.Pert.pert2v2.isCompact_Xc_segment_image d hΞ' (by linarith) hseg
  -- membership in the datum domain
  have hDE : ∀ x : ℝ, ((x : ℂ) + (y₀ : ℂ) * Complex.I) ∈ d.DE := by
    intro x
    have him : |((x : ℂ) + (y₀ : ℂ) * Complex.I).im| = y₀ := by
      simp [abs_of_pos hy₀pos]
    exact d.ends_sub _ (by rw [him]; exact hη')
  refine ⟨y₀, hYx, hΞy, hη', hdevZ, hKpc, ?_, ?_, ?_, ?_⟩
  · rintro ζ ⟨x, hx, rfl⟩
    have hb : d.φ ((x : ℂ) + (y₀ : ℂ) * Complex.I) ∈ MandelDim.ParabolicBasin f₀ D₀ := (hDE x).2
    have hne : d.φ ((x : ℂ) + (y₀ : ℂ) * Complex.I) ≠ 0 := by
      have := d.orbit_avoid _ hb 0
      simpa using this
    show MandelDim.tau0 (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)) ∈ _
    have heq : MandelDim.tau0 (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
        = d.φ ((x : ℂ) + (y₀ : ℂ) * Complex.I) := by
      simp only [Work.Pert.Xc, MandelDim.tau0]
      field_simp
    rw [heq]; exact hb
  · rintro ζ ⟨x, hx, rfl⟩
    rw [Work.Pert.mem_Qreg_cone]
    obtain ⟨hre, him⟩ := re_im_of_near_axis (hdevZ x hx)
    have hre' := (abs_le.mp hre).1
    have him' := (abs_le.mp him).1
    have hpos : 0 ≤ (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)).im := by linarith
    rw [abs_of_nonneg hpos]
    linarith
  · exact isCompact_Icc.image (by fun_prop)
  · rintro w ⟨x, -, rfl⟩
    exact hDE x

end Work.Pert.pert2v2.LeadWire
