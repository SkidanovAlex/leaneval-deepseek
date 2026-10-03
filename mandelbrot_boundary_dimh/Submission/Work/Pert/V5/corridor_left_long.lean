import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.deriv_Phi_le_of_gate_marg

namespace Work.Pert.V5

open Set Metric

/-- **The long corridor of the left case (`Re z ≤ Re z₀`), `C₂`-free.**

When the horizontal corridor `[Re z, Re z₀]` at height `Im z₀` is *long*
(`14 (M + Ξ) < Re z₀ - Re z`) then the pin bound `‖z₀ + M‖ ≤ Kp (1 + log (2+M))` forces
`Kp (1 + log (2+M)) ≥ (6/7) (Re z₀ - Re z)`, so the corridor length is paid for by the `Kp`-slot.
On the corridor both gate marginals are `≥ 3/2` (`16 M ≤ mgA`, `2 Rde + 2 < mgB`), so the
`C₂`-free, data-independent derivative bound `‖deriv Φm‖ ≤ 1024`
(`Work.Pert.V5.deriv_Phi_le_of_gate_marg`) gives the displacement bound `1025 · length` along it. -/
theorem corridor_left_long {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M)))
    {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re) (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (hcase : z.re ≤ z₀.re)
    (hlong : 14 * (M + Ξ) < z₀.re - z.re) :
    ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
        - (Φm z₀ - z₀)‖
      ≤ (|z.im| / 8 - (1 / 150 + 1 / 31) * |z.im|
          + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)))
        + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  have hlogpos : 0 < 1 + Real.log (2 + M) := by
    have h2 : (1 : ℝ) ≤ 2 + M := by linarith [hM]
    have := Real.log_nonneg h2
    linarith
  -- ## Step 1: the corridor `[Re z, Re z₀] × {Im z₀}` lies in the gate
  have hqmem : ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α :=
    (band_margins hΞ hM hInF1 hα hQAdm z.re z₀.im hzlo hzhi).1
  have hz0' : ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    rw [Complex.re_add_im z₀]; exact hz₀
  have hseg : ∀ x ∈ Set.Icc z.re z₀.re,
      ((x : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    intro x hx
    refine slice_interval (s := z₀.im) (a := z.re) (b := z₀.re) (x := x) hqmem hz0' ?_
    rw [min_eq_left hcase, max_eq_right hcase]
    exact hx
  -- ## Step 2: on the corridor both marginals exceed `3/2`
  have hmarg : ∀ x ∈ Set.Icc z.re z₀.re,
      (3 : ℝ) / 2 ≤ min (mgA Ξ α ((x : ℂ) + (z₀.im : ℂ) * Complex.I))
                         (mgB Ξ ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) := by
    intro x hx
    have hAq : (16 * M : ℝ) ≤ mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) :=
      (band_margins hΞ hM hInF1 hα hQAdm z.re z₀.im hzlo hzhi).2.2
    have hBz : (2 * Rde + 2 : ℝ) < mgB Ξ z₀ := (zo_margins hRde hcl).2
    have hAle : mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
        ≤ mgA Ξ α ((x : ℂ) + (z₀.im : ℂ) * Complex.I) := by
      rw [mgA_re_im Ξ α z.re z₀.im, mgA_re_im Ξ α x z₀.im]
      linarith [hx.1]
    have hBle : mgB Ξ z₀ ≤ mgB Ξ ((x : ℂ) + (z₀.im : ℂ) * Complex.I) := by
      have h1 : mgB Ξ ((x : ℂ) + (z₀.im : ℂ) * Complex.I) = |z₀.im| - Ξ - x :=
        mgB_re_im Ξ x z₀.im
      have h2 : mgB Ξ z₀ = |z₀.im| - Ξ - z₀.re := rfl
      rw [h1, h2]
      linarith [hx.2]
    exact le_min (by linarith) (by linarith)
  -- ## Step 3: the `C₂`-free derivative bound on the corridor
  have hdbound : ∀ w ∈ Work.Pert.Qm Ξ α,
      (3 : ℝ) / 2 ≤ min (mgA Ξ α w) (mgB Ξ w) → ‖deriv Φm w‖ ≤ 1024 :=
    fun w hw hm =>
      deriv_Phi_le_of_gate_marg hΞ hrr hM hInF1 hα hQAdm hσ hnorm hu hu2 hτQ hNT hΦm hw hm
  have hpt : ∀ x ∈ Set.Icc z.re z₀.re,
      ‖deriv Φm ((x : ℂ) + (z₀.im : ℂ) * Complex.I) - 1‖ ≤ 1025 := by
    intro x hx
    have h1 := hdbound _ (hseg x hx) (hmarg x hx)
    have h2 : ‖deriv Φm ((x : ℂ) + (z₀.im : ℂ) * Complex.I) - 1‖
        ≤ ‖deriv Φm ((x : ℂ) + (z₀.im : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    rw [norm_one] at h2
    linarith
  -- ## Step 4: horizontal transport along the corridor
  have hdev : ‖(Φm z₀ - z₀)
        - (Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
            - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))‖ ≤ 1025 * (z₀.re - z.re) := by
    have hmain := dev_horiz_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α) (s := z₀.im)
      (a := z.re) (b := z₀.re) (g := fun _ : ℝ => (1025 : ℝ))
      hQopen hcase hseg hΦm.1 hpt continuousOn_const
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmain
    rw [Complex.re_add_im z₀] at hmain
    have : (z₀.re - z.re) * 1025 = 1025 * (z₀.re - z.re) := by ring
    rwa [this] at hmain
  -- ## Step 5: the corridor length is paid by the `Kp`-slot
  have hpin_re : |z₀.re + M| ≤ Kp * (1 + Real.log (2 + M)) := by
    have h := Complex.abs_re_le_norm (z₀ + (((M : ℝ)) : ℂ))
    rw [Complex.add_re, Complex.ofReal_re] at h
    exact le_trans h hpinbd
  have hx0 : z₀.re ≤ -M + Kp * (1 + Real.log (2 + M)) := by
    have := (abs_le.mp hpin_re).2
    linarith
  have hlen : z₀.re - z.re ≤ Kp * (1 + Real.log (2 + M)) + M + Ξ + 2 ^ 10 := by
    linarith [hx0, hzlo]
  have hK1 : (1 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
    have h1 : 0 ≤ 1 / Ξ := (one_div_pos.mpr hΞ).le
    have h2 : 0 ≤ 1 / rr := (one_div_pos.mpr hrr).le
    linarith [le_of_lt hΞ]
  have hconst : (1025 : ℝ) * (7 / 6) ≤ 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
    have hpow : (1196 : ℝ) ≤ 2 ^ 36 := by norm_num
    have hmul : (1 : ℝ) * 2 ^ 36 ≤ (1 + Ξ + 1 / Ξ + 1 / rr) * 2 ^ 36 :=
      mul_le_mul_of_nonneg_right hK1 (by norm_num)
    rw [one_mul] at hmul
    have htarget : (1025 : ℝ) * (7 / 6) ≤ 1196 := by norm_num
    calc (1025 : ℝ) * (7 / 6) ≤ 1196 := htarget
      _ ≤ 2 ^ 36 := hpow
      _ ≤ (1 + Ξ + 1 / Ξ + 1 / rr) * 2 ^ 36 := hmul
      _ = 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) := by ring
  have hKpL : 0 ≤ Kp * (1 + Real.log (2 + M)) := mul_nonneg hKp hlogpos.le
  have hfinal : (1025 : ℝ) * (z₀.re - z.re)
      ≤ Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
    have hlen' : z₀.re - z.re ≤ 7 / 6 * (Kp * (1 + Real.log (2 + M))) := by
      linarith [hlen, hlong, hM, hΞ]
    have hstep : (1025 : ℝ) * (7 / 6) * (Kp * (1 + Real.log (2 + M)))
        ≤ 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (Kp * (1 + Real.log (2 + M))) :=
      mul_le_mul_of_nonneg_right hconst hKpL
    calc (1025 : ℝ) * (z₀.re - z.re)
        ≤ 1025 * (7 / 6 * (Kp * (1 + Real.log (2 + M)))) :=
          mul_le_mul_of_nonneg_left hlen' (by norm_num)
      _ = 1025 * (7 / 6) * (Kp * (1 + Real.log (2 + M))) := by ring
      _ ≤ 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (Kp * (1 + Real.log (2 + M))) := hstep
      _ = Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by ring
  -- ## Step 6: the two remaining summands are nonnegative
  have hRHS : Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
      ≤ (|z.im| / 8 - (1 / 150 + 1 / 31) * |z.im|
          + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)))
        + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
    have h1 : 0 ≤ |z.im| / 8 - (1 / 150 + 1 / 31) * |z.im| := by
      have hmul := mul_nonneg (show (0 : ℝ) ≤ 1 / 8 - (1 / 150 + 1 / 31) by norm_num)
        (abs_nonneg z.im)
      linarith [hmul]
    have h2 : 0 ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M)) := by
      have hΞ' : 0 ≤ 1 + Ξ := by linarith
      have h0 : 0 ≤ C₂ * 2 ^ 6 := mul_nonneg hC₂.le (by norm_num)
      exact mul_nonneg (mul_nonneg h0 hΞ') hlogpos.le
    have h3 : 0 ≤ 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) := by
      have hlog2 : 0 ≤ 1 + Real.log (2 + 16 * (M + 2 + Ξ)) := by
        have h2' : (1 : ℝ) ≤ 2 + 16 * (M + 2 + Ξ) := by linarith [hΞ, hM]
        have := Real.log_nonneg h2'
        linarith
      have h0 : 0 ≤ 2 ^ 24 * (1 + 1 / rr) :=
        mul_nonneg (by positivity) (by linarith [one_div_pos.mpr hrr])
      exact mul_nonneg h0 hlog2
    linarith [h1, h2, h3]
  -- ## Step 7: assemble
  have key : ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
          - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) - (Φm z₀ - z₀)‖
      ≤ 1025 * (z₀.re - z.re) := by
    rw [norm_sub_rev (Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
      - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) (Φm z₀ - z₀)]
    exact hdev
  exact le_trans key (le_trans hfinal hRHS)

end Work.Pert.V5
