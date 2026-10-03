import Mathlib
import Submission.Work.Pert.V5.W2.Setup
import Submission.Work.Pert.V5.W2.case2esc

/-!
# `Work.Pert.V5.W2.case2esc_partial` — the long, escaped right corridor, walk room FAILING

This is the complement of `Work.Pert.V5.W2.case2esc`: the same "long corridor, pin to the left of
the window strip" configuration, but the walk room of the pin **fails**, i.e.

  `mgB Ξ z₀ < (17/16) (z.re - z₀.re + 1) + 1`     (`hroomfail`),

so the `F`-walk route is (at least directly) unavailable here.

**The observation that makes the case as easy as `case2esc`.**  `case2esc` used the walk room only
to bound the corridor length, `ℓ ≤ 3 Kp L` (`len_le_three_KpL`).  But the length bound is available
*unconditionally* from the pin and the band alone: the pin bound gives `z₀.re ≥ -(M + Kp L)`, the
band hypothesis gives `z.re ≤ -(Ξ + 2^10)`, so

  `ℓ = z.re - z₀.re ≤ Kp (1 + log (2+M)) + M - Ξ - 2^10`     (`Work.Pert.V5.rw_len_le`),

and the long hypothesis `16 (M+2+Ξ) < ℓ` then forces `15 M < Kp (1 + log (2+M))`, i.e.
`ℓ ≤ (16/15) Kp L < 3 Kp L`.  So the *same* proof as in `case2esc` applies verbatim once the length
bound is re-derived without `hroom`; the walk room is not needed at all.

The two ingredients (both reused from `case2esc.lean`, where they are proved sorry-free):

* `corridor_dev_linear_right` — the *data-independent, `C₂`-free* horizontal transport bound
  `‖D q - D z₀‖ ≤ 1025 ℓ`, valid because on the corridor the tent identity gives
  `min (mgA) (mgB) ≥ min (mgA z₀, mgB (z.re + i z₀.im)) > 3/2`, so the Koebe value-gap estimate
  `‖deriv Φm‖ ≤ 1024` (`deriv_Phi_le_of_gate_marg`) applies pointwise;
* `slot_le_Kp_slot` — the arithmetic `1025 ℓ ≤ Kp · 2^36 K L` from `ℓ ≤ 3 Kp L`.

The conclusion is the `(W)`/`(dev)` certificate with `W := 1025 ℓ`; the `(N)` conjunct with `N = 1`
is proved in the consumer (`corridor_right_wk2`, `N1_conjunct`).
-/

namespace Work.Pert.V5.W2

open Set Metric
open scoped _root_.Topology

noncomputable section

set_option maxHeartbeats 1000000
-- several hypotheses of the target (`hF`, `hDE`, `hroomfail`, …) are not needed by the proof: the
-- case is closed by the `C₂`-free transport bound plus the length bound, exactly as in `case2esc`.
set_option linter.unusedVariables false

/-! ## 1. The corridor length bound, without the walk room -/

/-- **The corridor length bound from the pin and the band alone.**  With `L := 1 + log (2 + M)`:

  `z.re - z₀.re ≤ Kp L + M - Ξ - 2^10`   (`rw_len_le`),

and the long hypothesis `16 (M + 2 + Ξ) < z.re - z₀.re` then forces `15 M < Kp L`, whence
`z.re - z₀.re ≤ M + Kp L ≤ (16/15) Kp L`. -/
lemma len_le_sixteen_fifteenth_KpL {Ξ M Kp : ℝ} {z₀ z : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M)))
    (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (hlong : 16 * (M + 2 + Ξ) < z.re - z₀.re) :
    z.re - z₀.re ≤ (16 / 15) * (Kp * (1 + Real.log (2 + M))) := by
  have hLpos : (0 : ℝ) < 1 + Real.log (2 + M) := by
    have h : (0 : ℝ) ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    linarith
  have hlen := Work.Pert.V5.rw_len_le (Ξ := Ξ) (M := M) (Kp := Kp) (z₀ := z₀) (x := z.re)
    hzhi hpinbd
  -- the long hypothesis kills `M`: `15 M < Kp L`
  have hKL : 15 * M < Kp * (1 + Real.log (2 + M)) := by linarith
  have hMle : M ≤ Kp * (1 + Real.log (2 + M)) / 15 := by linarith
  have hlen' : z.re - z₀.re < Kp * (1 + Real.log (2 + M)) + M := by linarith
  have hfin : Kp * (1 + Real.log (2 + M)) + M
      ≤ (16 / 15) * (Kp * (1 + Real.log (2 + M))) := by linarith
  linarith

/-! ## 2. The target -/

theorem case2esc_partial {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
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
    (hesc : z₀.re ≤ ((Ξ : ℂ) - 1 / α).re + 2)
    (hroomfail : Work.Pert.V5.mgB Ξ z₀ < (17 / 16 : ℝ) * (z.re - z₀.re + 1) + 1) :
    ∃ W : ℝ,
      W ≤ |z.im| / 8 - (1 / 150 + 1 / 31) * |z.im|
          + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
      ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
          - (Φm z₀ - z₀)‖
        ≤ W + 1 * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
  -- ## the `C₂`-free corridor deviation `‖D q - D z₀‖ ≤ 1025 ℓ`
  have hdev := corridor_dev_linear_right (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde)
    (α := α) (σ := σ) (u := u) (Φm := Φm) (z₀ := z₀) (z := z)
    hΞ hrr hM hRde hInF1 hα hQAdm hσ hnorm hu hu2 hτQ hNT hΦm hz₀ hcl hz hzlo hzhi hcase
  -- ## the length bound (no walk room needed!) and the `Kp`-slot
  have hCnn : (0 : ℝ) ≤ Kp * (1 + Real.log (2 + M)) :=
    mul_nonneg hKp (by
      have h : (0 : ℝ) ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
      linarith)
  have hlen := len_le_sixteen_fifteenth_KpL (Ξ := Ξ) (M := M) (Kp := Kp) (z₀ := z₀) (z := z)
    hΞ hM hKp hpinbd hzhi hlong
  have hlen3 : z.re - z₀.re ≤ 3 * (Kp * (1 + Real.log (2 + M))) := by
    nlinarith [hlen, hCnn]
  have hW := slot_le_Kp_slot (Ξ := Ξ) (rr := rr) (M := M) (Kp := Kp) (ℓ := z.re - z₀.re)
    hΞ hrr hM hKp hlen3
  refine ⟨1025 * (z.re - z₀.re), ?_, ?_⟩
  · -- the `|Im|`-slot contributes a nonnegative amount
    have hb : (0 : ℝ) ≤ |z.im| / 8 - (1 / 150 + 1 / 31) * |z.im| := by
      have hc : (1 / 150 + 1 / 31 : ℝ) ≤ 1 / 8 := by norm_num
      nlinarith [abs_nonneg z.im, hc]
    linarith
  · -- the `C₂`-`Lg` block is nonnegative
    have h1 : (0 : ℝ) ≤ 1 + Real.log (2 + M) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + M)
      linarith
    have h2 : (0 : ℝ) ≤ 1 + Real.log (2 + 16 * (M + 2 + Ξ)) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + 16 * (M + 2 + Ξ))
      linarith
    have h3 : (0 : ℝ) ≤ 1 + 1 / rr := by positivity
    have h4 : (0 : ℝ) ≤ 1 + Ξ := by linarith
    have hA : (0 : ℝ) ≤ C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC₂) (by norm_num)) h4) h1
    have hB : (0 : ℝ) ≤ 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) :=
      mul_nonneg (mul_nonneg (by norm_num) h3) h2
    have hP : (0 : ℝ) ≤ 1 * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
        + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
      linarith
    linarith

end

end Work.Pert.V5.W2
