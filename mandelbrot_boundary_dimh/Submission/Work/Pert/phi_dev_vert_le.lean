import Mathlib
import Submission.Work.Pert.Phi_dev_geom
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.liftF_defect_le_tauC
import Submission.Work.Pert.tauC_upper_decay
import Submission.Work.Pert.liftF_differentiableOn_gate
import Submission.Work.Pert.dev_vert_le
import Submission.Work.Pert.deriv_Phi_close_on_gate
import Submission.Work.Pert.integral_inv_shift_le_log
import Submission.Work.Pert.integral_exp_neg_mul_le
import Submission.Work.Pert.liftF_inv_defect_le_exp

namespace Work.Pert

open MandelDim Complex Metric Set
open scoped Topology

noncomputable section

/-- A tiny real lemma: `C / min a b ≤ C/a' + C/b'` when `0 < a' ≤ a`, `0 < b' ≤ b`, `0 ≤ C`. -/
private lemma div_min_le {C a b a' b' : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (haa : a' ≤ a) (hbb : b' ≤ b) :
    C / min a b ≤ C / a' + C / b' := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    have h1 : C / a ≤ C / a' := div_le_div_of_nonneg_left hC ha' haa
    have h2 : 0 ≤ C / b' := div_nonneg hC (le_of_lt hb')
    linarith
  · rw [min_eq_right h]
    have h1 : C / b ≤ C / b' := div_le_div_of_nonneg_left hC hb' hbb
    have h2 : 0 ≤ C / a' := div_nonneg hC (le_of_lt ha')
    linarith

theorem phi_dev_vert_le (hF : MandelDim.FatouStatement)
    {Ξ rr : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32)
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α)) :
    ∃ K Y : ℝ, 0 < K ∧ Ξ + 3 ≤ Y ∧
      ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → -(Ξ + 1) ≤ z.re → z.re ≤ 2 → Y ≤ z.im →
        ‖(Φm z - z) - (Φm ((z.re : ℂ) + (Y : ℂ) * Complex.I)
            - ((z.re : ℂ) + (Y : ℂ) * Complex.I))‖
          ≤ K * (1 + Ξ + Real.log (2 + z.im)) := by
  obtain ⟨Rde, C₁, C₂, hRde, hC₁, hC₂, hDE⟩ := hF.2.2.2.2.1
  have hαne : α ≠ 0 := by
    have h : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
    intro h0; rw [h0] at h; simp at h
  have hc0 : 2 * Ξ + 4 < (1 / α).re := by
    have h := hQAdm ((Ξ : ℂ) - 1 / α) (by simp) (-(Ξ : ℂ)) (by simp)
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re] at h
    linarith
  have hFlift : DifferentiableOn ℂ (liftF u σ α) (Qm Ξ α) :=
    liftF_differentiableOn_gate hΞ hrr hInF1 hα64 hQAdm hσ hnorm hu hu2 hτQ hNT
  obtain ⟨Cinv, κ, Yτ, hCinvpos, hκpos, hinv⟩ :=
    liftF_inv_defect_le_exp hΞ hrr hInF1 hα64 hσ hnorm hu hu2 hτQ hNT
  -- choose the height `Y` and the constant `K`
  set Y : ℝ := max (Ξ + 3)
      (max (Ξ + 2 + 2 * Rde) (max (-(1 / α).im + 2 * Rde) (Yτ + 1))) with hYdef
  have hY1 : Ξ + 3 ≤ Y := le_max_left _ _
  have hY2 : Ξ + 2 + 2 * Rde ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hY3 : -(1 / α).im + 2 * Rde ≤ Y :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hY4 : Yτ + 1 ≤ Y :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hYpos : 0 ≤ Y := le_trans (by linarith) hY1
  have hYlt : Yτ < Y := by linarith
  have hRde2 : 0 < 2 * Rde := by linarith
  set K : ℝ := max 1 (4 * C₂ + Cinv / κ) with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK4 : 4 * C₂ ≤ K := by
    have h : (4 : ℝ) * C₂ ≤ 4 * C₂ + Cinv / κ := by
      have : 0 ≤ Cinv / κ := div_nonneg (le_of_lt hCinvpos) (le_of_lt hκpos)
      linarith
    exact le_trans h (le_max_right _ _)
  have hKA : Cinv / κ ≤ K := by
    have h : Cinv / κ ≤ 4 * C₂ + Cinv / κ := by
      have : 0 ≤ (4 : ℝ) * C₂ := by linarith
      linarith
    exact le_trans h (le_max_right _ _)
  refine ⟨K, Y, hKpos, hY1, ?_⟩
  intro z hzQ hre1 hre2 him
  -- ## Geometry of the vertical segment
  have hmem : ∀ t ∈ Set.Icc Y z.im, ((z.re : ℂ) + (t : ℂ) * Complex.I) ∈ Qm Ξ α := by
    intro t ht
    have ht3 : Ξ + 3 ≤ t := le_trans hY1 ht.1
    have ht0 : 0 ≤ t := by linarith
    rw [mem_Qm_iff_g]
    constructor
    · rw [margA_vert]
      have h2 : 0 < 3 + |t + (1 / α).im| := by positivity
      have h3 : 3 + |t + (1 / α).im| ≤ z.re - Ξ + (1 / α).re + |t + (1 / α).im| := by
        linarith
      linarith
    · rw [margB_vert ht0]
      linarith
  have hmargA : ∀ t ∈ Set.Icc Y z.im,
      3 + |t + (1 / α).im| ≤ margA_g Ξ α ((z.re : ℂ) + (t : ℂ) * Complex.I) := by
    intro t ht
    rw [margA_vert]
    linarith
  have hmargB : ∀ t ∈ Set.Icc Y z.im,
      t - Ξ - 2 ≤ margB_g Ξ ((z.re : ℂ) + (t : ℂ) * Complex.I) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [le_trans hY1 ht.1]
    rw [margB_vert ht0]
    linarith
  -- ## The majorant
  set g : ℝ → ℝ := fun t => 2 * C₂ * (3 + |t + (1 / α).im|)⁻¹ + 2 * C₂ * (t - Ξ - 2)⁻¹
      + Cinv * Real.exp (-(κ * t)) with hgdef
  have hgcont : ContinuousOn g (Set.Icc Y z.im) := by
    rw [hgdef]
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · apply ContinuousOn.const_mul
        apply ContinuousOn.inv₀
        · fun_prop
        · intro t ht; positivity
      · apply ContinuousOn.const_mul
        apply ContinuousOn.inv₀
        · fun_prop
        · intro t ht
          have := ht.1
          have := hY1
          linarith
    · apply ContinuousOn.const_mul
      fun_prop
  -- ## The pointwise derivative bound
  have hgder : ∀ t ∈ Set.Icc Y z.im,
      ‖deriv Φm ((z.re : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ g t := by
    intro t ht
    have ht3 : Ξ + 3 ≤ t := le_trans hY1 ht.1
    set w : ℂ := (z.re : ℂ) + (t : ℂ) * Complex.I with hw
    have hwim : w.im = t := by simp [hw]
    have hwre : w.re = z.re := by simp [hw]
    have hwQ : w ∈ Qm Ξ α := hmem t ht
    have hA : 3 + |t + (1 / α).im| ≤ margA_g Ξ α w := hmargA t ht
    have hB : t - Ξ - 2 ≤ margB_g Ξ w := hmargB t ht
    have htd0 : 2 * Rde ≤ t + (1 / α).im := by
      have := le_trans hY3 ht.1
      linarith
    have hA2 : 2 * Rde ≤ margA_g Ξ α w := by
      have h3 : 2 * Rde ≤ 3 + |t + (1 / α).im| := by
        linarith [le_abs_self (t + (1 / α).im)]
      linarith
    have hB2 : 2 * Rde ≤ margB_g Ξ w := by
      have := le_trans hY2 ht.1
      linarith
    have hApos : 0 < margA_g Ξ α w := lt_of_lt_of_le hRde2 hA2
    have hBpos : 0 < margB_g Ξ w := lt_of_lt_of_le hRde2 hB2
    set R : ℝ := min (margA_g Ξ α w) (margB_g Ξ w) / 2 with hRdef
    have hRge : Rde ≤ R := by
      have hmin : 2 * Rde ≤ min (margA_g Ξ α w) (margB_g Ξ w) := le_min hA2 hB2
      rw [hRdef]
      linarith
    have hball : Metric.ball w R ⊆ Qm Ξ α := by
      apply ball_subset_Qm_of_margin
      · rw [hRdef]
        have := min_le_left (margA_g Ξ α w) (margB_g Ξ w)
        linarith
      · rw [hRdef]
        have := min_le_right (margA_g Ξ α w) (margB_g Ξ w)
        linarith
    set v : ℂ → ℂ := fun ζ => liftF u σ α ζ - ζ with hv
    have hvdiff : DifferentiableOn ℂ v (Metric.ball w R) := by
      have h1 : DifferentiableOn ℂ (fun ζ : ℂ => liftF u σ α ζ - ζ) (Metric.ball w R) :=
        (hFlift.mono hball).sub differentiableOn_id
      simpa only [v] using h1
    have hvnear : ∀ ζ ∈ Metric.ball w R, ‖v ζ - 1‖ < 1 / 4 := by
      intro ζ hζ
      have hζQ : ζ ∈ Qm Ξ α := hball hζ
      have hb : ‖v ζ - 1‖ ≤ 1 / 32 := by
        have he : v ζ - 1 = liftF u σ α ζ - (ζ + 1) := by simp only [v]; ring
        rw [he]; exact hNT ζ hζQ
      linarith
    have habel : ∀ ζ ∈ Metric.ball w R, ζ + v ζ ∈ Metric.ball w R →
        Φm (ζ + v ζ) = Φm ζ + 1 := by
      intro ζ hζ hζv
      have hζQ : ζ ∈ Qm Ξ α := hball hζ
      have he : ζ + v ζ = liftF u σ α ζ := by simp only [v]; ring
      have hFQ : liftF u σ α ζ ∈ Qm Ξ α := by rw [← he]; exact hball hζv
      have h := hΦm.2.2 ζ hζQ hFQ
      rwa [he]
    have hΦdiff : DifferentiableOn ℂ Φm (Metric.ball w R) := hΦm.1.mono hball
    have hΦinj : Set.InjOn Φm (Metric.ball w R) := hΦm.2.1.mono hball
    obtain ⟨_, hb2⟩ := hDE Φm v w R hRge hΦdiff hΦinj hvdiff hvnear habel
    -- `C₂ / R` in terms of the two margins
    have hmR : C₂ / R = 2 * C₂ / min (margA_g Ξ α w) (margB_g Ξ w) := by
      rw [hRdef]
      have hne : min (margA_g Ξ α w) (margB_g Ξ w) ≠ 0 := ne_of_gt (lt_min hApos hBpos)
      field_simp
    have hCm : C₂ / R ≤ 2 * C₂ * (3 + |t + (1 / α).im|)⁻¹ + 2 * C₂ * (t - Ξ - 2)⁻¹ := by
      rw [hmR]
      have ha' : 0 < 3 + |t + (1 / α).im| := by positivity
      have hb' : 0 < t - Ξ - 2 := by linarith
      have hmain := div_min_le (C := 2 * C₂) (a := margA_g Ξ α w) (b := margB_g Ξ w)
        (a' := 3 + |t + (1 / α).im|) (b' := t - Ξ - 2)
        (by linarith) hApos hBpos ha' hb' hA hB
      simpa only [div_eq_mul_inv] using hmain
    -- the inverse-defect term
    have hvinv : ‖1 / v w - 1‖ ≤ Cinv * Real.exp (-(κ * t)) := by
      have h := hinv w hwQ (by rw [hwim]; exact lt_of_lt_of_le hYlt ht.1)
      rw [hwim] at h
      simpa only [v, one_div, one_mul] using h
    have htri : ‖deriv Φm w - 1‖ ≤ C₂ / R + Cinv * Real.exp (-(κ * t)) := by
      have h : deriv Φm w - 1 = (deriv Φm w - 1 / v w) + (1 / v w - 1) := by ring
      rw [h]
      exact le_trans (norm_add_le _ _) (add_le_add hb2 hvinv)
    have hgoal : ‖deriv Φm w - 1‖ ≤ 2 * C₂ * (3 + |t + (1 / α).im|)⁻¹
        + 2 * C₂ * (t - Ξ - 2)⁻¹ + Cinv * Real.exp (-(κ * t)) := by linarith
    simpa only [hw, hgdef] using hgoal
  -- ## Integrate along the vertical segment
  have hQopen : IsOpen (Qm Ξ α) := by
    have h1 : IsOpen {z : ℂ | -|(z - ((Ξ : ℂ) - 1 / α)).im| < (z - ((Ξ : ℂ) - 1 / α)).re} :=
      isOpen_lt (by fun_prop) (by fun_prop)
    have h2 : IsOpen {z : ℂ | (z - (-(Ξ : ℂ))).re < |(z - (-(Ξ : ℂ))).im|} :=
      isOpen_lt (by fun_prop) (by fun_prop)
    have h3 := h1.inter h2
    convert h3 using 1
    ext u
    simp [Qm, MandelDim.Qreg]
  have hvert := dev_vert_le (Q := Qm Ξ α) (Φ := Φm) (x := z.re) (y₁ := Y) (y₂ := z.im)
    (g := g) hQopen him hmem hΦm.1 hgder hgcont
  -- ## Bound the integral
  have hI : ∫ t in Y..z.im, g t ≤ 4 * C₂ * Real.log (2 + z.im) + Cinv / κ := by
    have huic : Set.uIcc Y z.im = Set.Icc Y z.im := Set.uIcc_of_le him
    have hc1 : ContinuousOn (fun t : ℝ => 2 * C₂ * (3 + |t + (1 / α).im|)⁻¹)
        (Set.uIcc Y z.im) := by
      rw [Set.uIcc_of_le him]
      apply ContinuousOn.const_mul
      apply ContinuousOn.inv₀
      · fun_prop
      · intro t ht; positivity
    have hc2 : ContinuousOn (fun t : ℝ => 2 * C₂ * (t - Ξ - 2)⁻¹) (Set.uIcc Y z.im) := by
      rw [Set.uIcc_of_le him]
      apply ContinuousOn.const_mul
      apply ContinuousOn.inv₀
      · fun_prop
      · intro t ht; have := ht.1; have := hY1; linarith
    have hc3 : ContinuousOn (fun t : ℝ => Cinv * Real.exp (-(κ * t))) (Set.uIcc Y z.im) := by
      apply ContinuousOn.const_mul
      fun_prop
    have hi1 := hc1.intervalIntegrable (μ := MeasureTheory.volume)
    have hi2 := hc2.intervalIntegrable (μ := MeasureTheory.volume)
    have hi3 := hc3.intervalIntegrable (μ := MeasureTheory.volume)
    have hsplit : ∫ t in Y..z.im, g t
        = ((∫ t in Y..z.im, 2 * C₂ * (3 + |t + (1 / α).im|)⁻¹)
            + (∫ t in Y..z.im, 2 * C₂ * (t - Ξ - 2)⁻¹))
          + (∫ t in Y..z.im, Cinv * Real.exp (-(κ * t))) := by
      simp only [hgdef]
      rw [intervalIntegral.integral_add (hi1.add hi2) hi3,
        intervalIntegral.integral_add hi1 hi2]
    have hJ1 : ∫ t in Y..z.im, 2 * C₂ * (3 + |t + (1 / α).im|)⁻¹
        ≤ 2 * C₂ * Real.log (2 + z.im) := by
      rw [intervalIntegral.integral_const_mul]
      have hcongr : ∫ t in Y..z.im, (3 + |t + (1 / α).im|)⁻¹
          = ∫ t in Y..z.im, ((3 + (1 / α).im) + t)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le him] at ht
        have hpos : 0 ≤ t + (1 / α).im := by have := le_trans hY3 ht.1; linarith
        show (3 + |t + (1 / α).im|)⁻¹ = ((3 + (1 / α).im) + t)⁻¹
        rw [abs_of_nonneg hpos]
        ring_nf
      rw [hcongr]
      exact mul_le_mul_of_nonneg_left
        (integral_inv_shift_le_log hYpos him (by linarith [hY3, hRde])) (by linarith)
    have hJ2 : ∫ t in Y..z.im, 2 * C₂ * (t - Ξ - 2)⁻¹ ≤ 2 * C₂ * Real.log (2 + z.im) := by
      rw [intervalIntegral.integral_const_mul]
      have hcongr : ∫ t in Y..z.im, (t - Ξ - 2)⁻¹
          = ∫ t in Y..z.im, ((-(Ξ + 2)) + t)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        show (t - Ξ - 2)⁻¹ = ((-(Ξ + 2)) + t)⁻¹
        ring_nf
      rw [hcongr]
      exact mul_le_mul_of_nonneg_left
        (integral_inv_shift_le_log hYpos him (by linarith [hY1])) (by linarith)
    have hJ3 : ∫ t in Y..z.im, Cinv * Real.exp (-(κ * t)) ≤ Cinv / κ := by
      rw [intervalIntegral.integral_const_mul]
      have h := integral_exp_neg_mul_le hκpos hYpos him
      have h3 : Cinv * (∫ t in Y..z.im, Real.exp (-(κ * t))) ≤ Cinv * (1 / κ) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hCinvpos)
      simpa only [mul_one_div] using h3
    rw [hsplit]
    linarith
  -- ## Assemble
  have hLHS : (Φm ((z.re : ℂ) + (z.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z.im : ℂ) * Complex.I))
      = Φm z - z := by rw [Complex.re_add_im]
  have hstep : ‖(Φm z - z) - (Φm ((z.re : ℂ) + (Y : ℂ) * Complex.I)
      - ((z.re : ℂ) + (Y : ℂ) * Complex.I))‖ ≤ ∫ t in Y..z.im, g t := by
    rw [← hLHS]
    exact hvert
  have hlog : 0 ≤ Real.log (2 + z.im) := Real.log_nonneg (by linarith)
  have hfin : ‖(Φm z - z) - (Φm ((z.re : ℂ) + (Y : ℂ) * Complex.I)
      - ((z.re : ℂ) + (Y : ℂ) * Complex.I))‖ ≤ K * (1 + Ξ + Real.log (2 + z.im)) := by
    have h1 := hstep
    have h2 := hI
    have h3 : (1 : ℝ) ≤ 1 + Ξ + Real.log (2 + z.im) := by linarith
    nlinarith [h1, h2, h3, hK4, hKA, hKpos, hlog, hΞ]
  exact hfin

end

end Work.Pert
