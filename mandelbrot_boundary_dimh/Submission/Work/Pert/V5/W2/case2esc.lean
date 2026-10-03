import Mathlib
import Submission.Work.Pert.V5.W2.Setup
import Submission.Work.Pert.V5.deriv_Phi_le_of_gate_marg
import Submission.Work.Pert.V5.dev_horiz_le

/-!
# `Work.Pert.V5.W2.case2esc` — the long, escaped right corridor

This is the "long corridor that starts to the left of the window strip" case of the right corridor
of `Work.Pert.V5.corridor_right_wk2`.  We prove the `(W)`/`(dev)` certificate

```
∃ W,  W ≤ |z.im|/8 - (1/150+1/31)|z.im| + Kp 2^36 K L
      ∧ ‖D q - D z₀‖ ≤ W + (C₂ 2^6 (1+Ξ) L + 2^24 (1+1/rr) Lg)
```

with `q = z.re + i z₀.im`, `L = 1 + log (2+M)`, `Lg = 1 + log (2 + 16(M+2+Ξ))`,
`K = 1 + Ξ + 1/Ξ + 1/rr`.

**The route is the crude, `C₂`-free one**, and this is essential: the allowance in which `W` must
fit (`Kp 2^36 K L`) contains no `C₂`, and `C₂` is an unconstrained input, so no `C₂`-dependent
estimate of the horizontal deviation can be charged to it.  Two `C₂`-free inputs suffice:

* `corridor_dev_linear_right`: along the horizontal corridor at height `z₀.im`, whose left endpoint
  is the pin `z₀` and whose right endpoint sits at a *band* abscissa, the margin
  `min (mgA) (mgB)` is `≥ 3/2` (the `mgA`-margin is monotone increasing from
  `mgA z₀ > 2 Rde + 2`, the `mgB`-margin is monotone decreasing to `≥ 2^10` by `band_margins`).
  Hence the data-independent derivative bound `‖deriv Φm‖ ≤ 1024`
  (`Work.Pert.V5.deriv_Phi_le_of_gate_marg`, the Koebe value-gap estimate with an explicit constant)
  gives the displacement bound `1025 · length` (`dev_horiz_le`).
* `len_le_three_KpL`: the corridor length `ℓ = z.re - z₀.re` is at most `3 Kp L`.  Indeed the walk
  room `hroom` bounds `(17/16)(ℓ+1) + 1 ≤ mgB z₀ = |y₀| - Ξ - x₀ ≤ 2 Kp L + M - Ξ` by the pin bound
  (`rw_pin_re_im`), and the length hypothesis `hlong` then forces `Kp L > 7.5 M`, so that
  `ℓ ≤ 2 Kp L + M < 3 Kp L`.

Then `1025 ℓ ≤ 3075 Kp L ≤ Kp · 2^36 K L` (`3075 ≤ 2^36 ≤ 2^36 K`, `K ≥ 1`), which is the `(W)`
slot; and the `(dev)` conjunct follows since the `C₂`-`Lg` block is nonnegative.

Note that the walk/window machinery (`hroom` is the *walk room*) is not needed for the deviation
itself: the crude bound is what fits the allowance, and it needs `hroom` only for the length bound.
-/

namespace Work.Pert.V5.W2

open Set Metric
open scoped _root_.Topology

noncomputable section

set_option maxHeartbeats 1000000

set_option linter.unusedVariables false

/-! ## 1. The crude `C₂`-free horizontal transport on the right corridor -/

/-- **Crude horizontal transport of the deviation along the right corridor.**

If `z₀.re ≤ z.re` and `z` has a band abscissa, then, along the horizontal corridor at height
`z₀.im` joining `z₀` to `(z.re, z₀.im)`, the margin `min (mgA) (mgB)` is at least `3/2`
(the `mgA`-margin grows from `mgA z₀ > 2 Rde + 2`, the `mgB`-margin decays only down to
`≥ 2^10` at the band end); the data-independent value-gap estimate `‖deriv Φm‖ ≤ 1024` therefore
applies pointwise and

  `‖D (z.re + i z₀.im) - D z₀‖ ≤ 1025 (z.re - z₀.re)`.

This is the mirror (right case) of `Work.Pert.V5.corridor_dev_linear`, and — like it — it uses
neither `C₂` nor any `F`-orbit. -/
theorem corridor_dev_linear_right {Ξ rr M Rde : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ z : ℂ}
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
    (hcase : z₀.re ≤ z.re) :
    ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
        - (Φm z₀ - z₀)‖ ≤ 1025 * (z.re - z₀.re) := by
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  -- ## the two endpoints of the corridor
  have hqmem : ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α :=
    (band_margins hΞ hM hInF1 hα hQAdm z.re z₀.im hzlo hzhi).1
  have hz0' : ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    rw [Complex.re_add_im z₀]; exact hz₀
  have hseg : ∀ x ∈ Set.Icc z₀.re z.re,
      ((x : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    intro x hx
    refine slice_interval (s := z₀.im) (a := z.re) (b := z₀.re) (x := x) hqmem hz0' ?_
    rw [min_eq_right hcase, max_eq_left hcase]
    exact hx
  -- ## the margin is `≥ 3/2` along the corridor (tent structure)
  have hmarg : ∀ x ∈ Set.Icc z₀.re z.re,
      (3 : ℝ) / 2 ≤ min (mgA Ξ α ((x : ℂ) + (z₀.im : ℂ) * Complex.I))
                         (mgB Ξ ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) := by
    intro x hx
    have hA0 : 2 * Rde + 2 < mgA Ξ α z₀ := (zo_margins hRde hcl).1
    have hBq : (2 : ℝ) ^ 10 ≤ mgB Ξ ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) :=
      (band_margins hΞ hM hInF1 hα hQAdm z.re z₀.im hzlo hzhi).2.1
    have hAle : mgA Ξ α z₀ ≤ mgA Ξ α ((x : ℂ) + (z₀.im : ℂ) * Complex.I) := by
      have h1 : mgA Ξ α ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) = mgA Ξ α z₀ := by
        rw [Complex.re_add_im]
      rw [← h1, mgA_re_im Ξ α z₀.re z₀.im, mgA_re_im Ξ α x z₀.im]
      linarith [hx.1]
    have hBle : mgB Ξ ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
        ≤ mgB Ξ ((x : ℂ) + (z₀.im : ℂ) * Complex.I) := by
      rw [mgB_re_im Ξ z.re z₀.im, mgB_re_im Ξ x z₀.im]
      linarith [hx.2]
    exact le_min (by linarith) (by linarith)
  -- ## the `C₂`-free derivative bound on the corridor
  have hdbound : ∀ w ∈ Work.Pert.Qm Ξ α,
      (3 : ℝ) / 2 ≤ min (mgA Ξ α w) (mgB Ξ w) → ‖deriv Φm w‖ ≤ 1024 :=
    fun w hw hm =>
      deriv_Phi_le_of_gate_marg hΞ hrr hM hInF1 hα hQAdm hσ hnorm hu hu2 hτQ hNT hΦm hw hm
  have hpt : ∀ x ∈ Set.Icc z₀.re z.re,
      ‖deriv Φm ((x : ℂ) + (z₀.im : ℂ) * Complex.I) - 1‖ ≤ 1025 := by
    intro x hx
    have h1 := hdbound _ (hseg x hx) (hmarg x hx)
    have h2 : ‖deriv Φm ((x : ℂ) + (z₀.im : ℂ) * Complex.I) - 1‖
        ≤ ‖deriv Φm ((x : ℂ) + (z₀.im : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    rw [norm_one] at h2
    linarith
  -- ## horizontal transport
  have hmain := dev_horiz_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α) (s := z₀.im)
    (a := z₀.re) (b := z.re) (g := fun _ : ℝ => (1025 : ℝ))
    hQopen hcase hseg hΦm.1 hpt continuousOn_const
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmain
  rw [Complex.re_add_im z₀] at hmain
  have he : (z.re - z₀.re) * 1025 = 1025 * (z.re - z₀.re) := by ring
  rw [he] at hmain
  exact hmain

/-! ## 2. The corridor length is at most `3 Kp L` -/

/-- **The corridor length bound.**  From the walk room `hroom`
(`(17/16)(ℓ+1) + 1 ≤ mgB z₀`) and the pin bound `‖z₀ + M‖ ≤ Kp L` one gets

  `ℓ = z.re - z₀.re ≤ 2 Kp L + M`,

and then the long-corridor hypothesis `16 (M+2+Ξ) < ℓ` forces `2 Kp L > 15 M + 32 + 16 Ξ`, whence
`M < (2/15) Kp L` and `ℓ ≤ 2 Kp L + M < 3 Kp L`. -/
theorem len_le_three_KpL {Ξ M Kp : ℝ} {z₀ z : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M)))
    (hroom : (17 / 16 : ℝ) * (z.re - z₀.re + 1) + 1 ≤ Work.Pert.V5.mgB Ξ z₀)
    (hlong : 16 * (M + 2 + Ξ) < z.re - z₀.re) :
    z.re - z₀.re ≤ 3 * (Kp * (1 + Real.log (2 + M))) := by
  set L : ℝ := 1 + Real.log (2 + M) with hL
  have hLpos : 0 < L := by
    rw [hL]
    have h : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    linarith
  obtain ⟨hre, him⟩ := Work.Pert.V5.rw_pin_re_im hpinbd
  have hre' : -(Kp * L) ≤ z₀.re + M := (abs_le.mp hre).1
  have hB : Work.Pert.V5.mgB Ξ z₀ ≤ 2 * (Kp * L) + M - Ξ := by
    simp only [Work.Pert.V5.mgB]
    linarith [him, hre']
  have h1 : (17 / 16 : ℝ) * (z.re - z₀.re + 1) + 1 ≤ 2 * (Kp * L) + M - Ξ := by
    linarith [hroom, hB]
  have hKLnn : 0 ≤ Kp * L := mul_nonneg hKp (le_of_lt hLpos)
  have h3 : z.re - z₀.re ≤ 2 * (Kp * L) + M := by linarith [h1, hKLnn, hΞ]
  have h4 : 15 * M + 32 + 16 * Ξ < 2 * (Kp * L) := by linarith [hlong, h3]
  have h5 : M < 2 * (Kp * L) / 15 := by linarith [h4, hΞ]
  have h6 : z.re - z₀.re ≤ 3 * (Kp * L) := by linarith [h3, h5, hKLnn]
  rw [hL] at h6 ⊢
  exact h6

/-! ## 3. The arithmetic: the crude cost fits the `Kp`-slot -/

/-- **The crude corridor cost `1025 ℓ` fits the `Kp`-slot** as soon as `ℓ ≤ 3 Kp L`:
`1025 · 3 = 3075 ≤ 2^36 ≤ 2^36 K`. -/
theorem slot_le_Kp_slot {Ξ rr M Kp ℓ : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hKp : 0 ≤ Kp)
    (hlen : ℓ ≤ 3 * (Kp * (1 + Real.log (2 + M)))) :
    1025 * ℓ ≤ Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
  set L : ℝ := 1 + Real.log (2 + M) with hL
  set K : ℝ := 1 + Ξ + 1 / Ξ + 1 / rr with hK
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    linarith
  have hLnn : 0 ≤ L := le_trans zero_le_one hL1
  have hK1 : 1 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ 1 / Ξ := by positivity
    have h2 : 0 ≤ 1 / rr := by positivity
    linarith
  have hKLnn : 0 ≤ Kp * L := mul_nonneg hKp hLnn
  have hbig : (3075 : ℝ) ≤ 2 ^ 36 * K := by
    have h2 : (3075 : ℝ) ≤ 2 ^ 36 := by norm_num
    nlinarith [hK1, h2]
  have h1 : 1025 * ℓ ≤ 3075 * (Kp * L) := by linarith [hlen]
  have h2 : (3075 : ℝ) * (Kp * L) ≤ (2 ^ 36 * K) * (Kp * L) :=
    mul_le_mul_of_nonneg_right hbig hKLnn
  have h3 : (2 ^ 36 * K) * (Kp * L) = Kp * 2 ^ 36 * K * L := by ring
  rw [h3] at h2
  linarith [h1, h2]

/-! ## 4. The target -/

theorem case2esc {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
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
    (hroom : (17 / 16 : ℝ) * (z.re - z₀.re + 1) + 1 ≤ Work.Pert.V5.mgB Ξ z₀) :
    ∃ W : ℝ,
      W ≤ |z.im| / 8 - (1 / 150 + 1 / 31) * |z.im|
          + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
      ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
          - (Φm z₀ - z₀)‖
        ≤ W + 1 * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
  -- ## the `C₂`-free corridor deviation
  have hdev := corridor_dev_linear_right (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde)
    (α := α) (σ := σ) (u := u) (Φm := Φm) (z₀ := z₀) (z := z)
    hΞ hrr hM hRde hInF1 hα hQAdm hσ hnorm hu hu2 hτQ hNT hΦm hz₀ hcl hz hzlo hzhi hcase
  -- ## the length bound and the `Kp`-slot
  have hlen := len_le_three_KpL (Ξ := Ξ) (M := M) (Kp := Kp) (z₀ := z₀) (z := z)
    hΞ hM hKp hpinbd hroom hlong
  have hW := slot_le_Kp_slot (Ξ := Ξ) (rr := rr) (M := M) (Kp := Kp) (ℓ := z.re - z₀.re)
    hΞ hrr hM hKp hlen
  refine ⟨1025 * (z.re - z₀.re), ?_, ?_⟩
  · -- the `|Im|`-slot contributes a nonnegative amount
    have hb : (0 : ℝ) ≤ |z.im| / 8 - (1 / 150 + 1 / 31) * |z.im| := by
      have hc : (1 / 150 + 1 / 31 : ℝ) ≤ 1 / 8 := by norm_num
      have hx : (0 : ℝ) ≤ |z.im| := abs_nonneg _
      have hm : (0 : ℝ) ≤ 1 / 8 - (1 / 150 + 1 / 31) := by linarith
      have h := mul_nonneg hx hm
      linarith [h]
    linarith [hW, hb]
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
      linarith [hA, hB]
    linarith [hdev, hP]

end

end Work.Pert.V5.W2
