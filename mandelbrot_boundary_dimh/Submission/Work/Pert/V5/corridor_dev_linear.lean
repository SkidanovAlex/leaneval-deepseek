import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.dev_horiz_le
import Submission.Work.Pert.V5.deriv_Phi_le_of_gate_marg

set_option linter.unusedVariables false

/-!
# `Work.Pert.V5.corridor_dev_linear`

The **linear** transport of the deviation `D w = Φm w - w` of a Fatou coordinate `Φm` of the
near-translation `F = liftF u σ α` on the gate `Qm Ξ α`, along the horizontal corridor at height
`z₀.im` joining `z.re + i z₀.im` to `z₀`.

The corridor has its left endpoint in the band `[-(Ξ+2^10+2M), -(Ξ+2^10)] × ℝ`, hence by
`band_margins` both gate marginals there are large (`mgB ≥ 2^10`, `mgA ≥ 16 M`); the right endpoint
is the pin `z₀`, whose margins are `> 2 Rde + 2` by `zo_margins`.  Since `mgA` is increasing and
`mgB` decreasing in the abscissa, the margin `min (mgA) (mgB)` stays `≥ 3/2` on the whole corridor;
so the data-independent, `C₂`-free derivative bound `‖deriv Φm‖ ≤ 1024`
(`deriv_Phi_le_of_gate_marg`) holds there, and the fundamental estimate applied along the corridor
(`dev_horiz_le`) gives the displacement bound `1025 · length`. -/

namespace Work.Pert.V5

open Set Metric

theorem corridor_dev_linear {Ξ rr M Rde : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ z : ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hRde : 0 < Rde)
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
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re) (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (hcase : z.re ≤ z₀.re) :
    ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
        - (Φm z₀ - z₀)‖ ≤ 1025 * (z₀.re - z.re) := by
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
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
  -- ## Step 5: assemble
  rw [norm_sub_rev (Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
    - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) (Φm z₀ - z₀)]
  exact hdev

end Work.Pert.V5
