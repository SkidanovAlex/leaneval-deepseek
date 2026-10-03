import Mathlib
import Submission.Work.Pert.V5.W2.Setup

/-!
# `Work.Pert.V5.W2.case2win` — the "long corridor inside the window" case

This is the case of the right corridor in which the pin `z₀` already lies strictly inside the
window strip `Ξ - (1/α).re + 1 < Re < -Ξ - 3` (`hwin` says `Ξ - (1/α).re + 2 < z₀.re`).
Then the *whole* corridor `[z₀.re, z.re]` at height `z₀.im` lies in the window strip: its left end
is `> Ξ - (1/α).re + 1` and its right end is at a band abscissa, hence `< -Ξ - 3`.  So the
C₂-free window transport bound `window_horiz_dev_le` (constant `1/150 + 1/31`) applies to the whole
corridor, which proves the first conjunct, and the second conjunct is the elementary arithmetic
fact that in the *long* case (`hlong`, which forces `Kp (1+log(2+M)) > 15 M` through the pin bound
`rw_len_le`) the linear cost `(1/150+1/31) ℓ` fits into the slot
`Kp 2^36 (1 + Ξ + 1/Ξ + 1/rr) (1 + log (2+M))`.
-/

namespace Work.Pert.V5.W2

open Set Metric Filter
open scoped _root_.Topology

/-- **The arithmetic of the win.**  In the long case `16 (M+2+Ξ) < ℓ` the pin length bound
`ℓ ≤ Kp (1+log(2+M)) + M` forces `15 M < Kp (1+log(2+M))`; hence `ℓ ≤ (16/15) Kp L` and the linear
cost `(1/150+1/31) ℓ < (4/45) Kp L` is swallowed by the slot `Kp 2^36 K L`. -/
private lemma case2win_arith {Ξ rr M Kp ℓ : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hKp : 0 ≤ Kp)
    (hlen : ℓ ≤ Kp * (1 + Real.log (2 + M)) + M)
    (hlong : 16 * (M + 2 + Ξ) < ℓ) :
    (1 / 150 + 1 / 31) * ℓ
      ≤ Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
  set L : ℝ := 1 + Real.log (2 + M) with hL
  set K : ℝ := 1 + Ξ + 1 / Ξ + 1 / rr with hK
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    have h : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    linarith
  have hLnn : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hK]
    have h1 : 0 ≤ 1 / Ξ := by positivity
    have h2 : 0 ≤ 1 / rr := by positivity
    linarith
  have hKL : (0 : ℝ) ≤ Kp * L := mul_nonneg hKp hLnn
  have hlen' : ℓ ≤ Kp * L + M := by rw [hL] at hlen ⊢; linarith
  have hstep : 15 * M < Kp * L := by linarith
  have hMlt : M < Kp * L / 15 := by linarith
  have hℓ : ℓ ≤ Kp * L * (16 / 15) := by nlinarith
  have hc0 : (1 / 150 + 1 / 31 : ℝ) ≤ 1 / 12 := by norm_num
  have hmain : (1 / 150 + 1 / 31) * ℓ ≤ (4 / 45) * (Kp * L) := by
    calc (1 / 150 + 1 / 31) * ℓ ≤ (1 / 12) * (Kp * L * (16 / 15)) :=
          mul_le_mul hc0 hℓ (by linarith) (by norm_num)
      _ = (4 / 45) * (Kp * L) := by ring
  have hconst : (4 / 45 : ℝ) ≤ 2 ^ 36 * K := by
    have h2 : (1 : ℝ) ≤ 2 ^ 36 := by norm_num
    nlinarith
  have hfin : (4 / 45 : ℝ) * (Kp * L) ≤ 2 ^ 36 * K * (Kp * L) :=
    mul_le_mul_of_nonneg_right hconst hKL
  rw [hK]
  calc (1 / 150 + 1 / 31) * ℓ ≤ (4 / 45) * (Kp * L) := hmain
    _ ≤ 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (Kp * L) := hfin
    _ = Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
        rw [hL]; ring

theorem case2win {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M)))
    {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re) (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (ht : 4 * Rde ≤ |z.im|) (hcase : z₀.re ≤ z.re)
    (hlong : 16 * (M + 2 + Ξ) < z.re - z₀.re)
    (hwin : ((Ξ : ℂ) - 1 / α).re + 2 < z₀.re) :
    (‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
        - (Φm z₀ - z₀)‖ ≤ (1 / 150 + 1 / 31) * (z.re - z₀.re)) ∧
      ((1 / 150 + 1 / 31) * (z.re - z₀.re)
        ≤ Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))) := by
  have hre : ((Ξ : ℂ) - 1 / α).re = Ξ - (1 / α).re := by
    rw [Complex.sub_re, Complex.ofReal_re]
  constructor
  · -- the whole corridor lies in the window strip
    have hwin' : ∀ x ∈ Set.Icc z₀.re z.re, ((Ξ : ℂ) - 1 / α).re + 1 < x ∧ x < -Ξ - 3 := by
      intro x hx
      refine ⟨by linarith [hx.1, hwin], ?_⟩
      have h2 : z.re < -Ξ - 3 := by
        have h210 : (3 : ℝ) < 2 ^ 10 := by norm_num
        linarith
      linarith [hx.2]
    have hseg : ∀ x ∈ Set.Icc z₀.re z.re,
        ((x : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
      intro x hx
      have hxlo : ((Ξ : ℂ) - 1 / α).re + 1 < x := (hwin' x hx).1
      have hxhi : x < -Ξ - 3 := (hwin' x hx).2
      rw [Work.Pert.V5.mem_Qm_iff_mg]
      refine ⟨?_, ?_⟩
      · rw [Work.Pert.V5.mgA_re_im]
        rw [hre] at hxlo
        linarith [abs_nonneg (z₀.im + (1 / α).im)]
      · rw [Work.Pert.V5.mgB_re_im]
        linarith [abs_nonneg z₀.im]
    have hmain := Work.Pert.V5.window_horiz_dev_le (s := z₀.im) (a := z₀.re) (b := z.re)
      hF hQAdm hNT hΦm hseg hwin' hcase
    simpa [Complex.re_add_im] using hmain
  · -- the linear cost is paid by the `Kp`-slot
    have hlen : z.re - z₀.re ≤ Kp * (1 + Real.log (2 + M)) + M := by
      have h := Work.Pert.V5.rw_len_le (Ξ := Ξ) (M := M) (Kp := Kp) (z₀ := z₀) (x := z.re)
        hzhi hpinbd
      linarith
    exact case2win_arith hΞ hrr hM hKp hlen hlong

end Work.Pert.V5.W2
