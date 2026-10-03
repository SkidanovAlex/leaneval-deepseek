import Mathlib
import Submission.Work.Pert.Gates
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.WaistPinned.waist_disc_window
import Submission.Work.Pert.pert2v2.norm_sub_le_two_mul_of_deriv_sub_one
import Submission.Work.Analysis.PertCrux.gate_fatou_lipschitz

/-!
# `Work.Pert.pert2v2.HresFixed` — the segment residual at a *fixed* height, via the waist disc

The (A.4.4) row of `pert2_v2` needs the residual

  `‖Φp ς - d.E W‖ < δ`  for `W = x + i y₀` (`x ∈ [0,1)`) and every gate preimage `ς` of `W`,

at a height `y₀` that is fixed *before* the perturbation enters.  The two geometric facts that make
this possible without any height threshold depending on `α` are

* `Work.Pert.WaistPinned.waist_disc_window`: the disc of radius `ρ` about the axis point `i T` lies
  in *both* gates as soon as `Ξ + 2 ρ < T` (no `1/α`-term!),
* the *mean value* form of the modulus of injectivity (`norm_sub_le_two_mul_of_deriv_sub_one`): on a
  convex set inside the gate where `‖deriv Φ - 1‖ ≤ 1/2`, `Φ` is `2`-antilipschitz.

Hence: the preimage `ς` of `W` (which the disc cover localises in `closedBall (i y₀) (y₀/8)`) and
the curve point `Z = Xc d W = τ₀ (d.φ W)` (localised by the logarithmic deviation) are both in the
waist disc, on which the modulus gives `‖ς - Z‖ ≤ 2 ‖Φm ς - Φm Z‖ = 2 ‖W - Φm Z‖ < 2 εp` (the
pinning `(RIG)`), and the pin of `Φp` at `Z` transfers the bound to `ς` by the gate Lipschitz bound.
-/

namespace Work.Pert.pert2v2

open _root_.MandelDim Complex Set Metric

noncomputable section

/-- **The thickened segment inside the waist disc.**  If `x` and `y` lie in the disc of radius
`ρ - R₂` about the axis point `i T`, the `R₂`-thickening of the segment from `x` to `y` lies in the
disc of radius `ρ`, hence — by `waist_disc_window` — in both gates `Qm Ξ α`, `Qp Ξ α` as soon as
`Ξ + 2 ρ < T`. -/
theorem waist_tube_gates {Ξ T ρ R₂ : ℝ} {α : ℂ} {x y : ℂ}
    (hF1 : MandelDim.InF1 α) (hT : 0 < T) (hρ : 0 ≤ ρ) (hR₂ : 0 ≤ R₂)
    (hwaist : Ξ + 2 * ρ < T)
    (hx : ‖x - T * Complex.I‖ ≤ ρ - R₂) (hy : ‖y - T * Complex.I‖ ≤ ρ - R₂) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Metric.closedBall ((1 - t) * x + t * y) R₂ ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) ∧
      Metric.ball (T * Complex.I) (ρ - R₂) ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := by
  have hz₀re : (T * Complex.I).re = 0 := by simp
  have hz₀im : |(T * Complex.I).im| = T := by simp [abs_of_pos hT]
  have hdisc : Metric.closedBall (T * Complex.I) ρ ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α :=
    Work.Pert.WaistPinned.waist_disc_window (ξ := Ξ) (T := T) (ρ := ρ) (α := α)
      (z₀ := T * Complex.I) hF1 hρ hwaist hz₀re hz₀im
  have hmem : ∀ z : ℂ, ‖z - T * Complex.I‖ ≤ ρ → z ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := by
    intro z hz
    refine hdisc ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hz
  constructor
  · intro t ht z hz
    refine hmem z ?_
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h1 : ‖(1 - t) * x + t * y - T * Complex.I‖
        ≤ (1 - t) * ‖x - T * Complex.I‖ + t * ‖y - T * Complex.I‖ := by
      have hcast : ((1 - t : ℝ) : ℂ) = 1 - (t : ℂ) := by push_cast; ring
      have hid : (1 - t) * x + t * y - T * Complex.I
          = ((1 - t : ℝ) : ℂ) * (x - T * Complex.I) + ((t : ℝ) : ℂ) * (y - T * Complex.I) := by
        rw [hcast]; ring
      rw [hid]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul,
        show ‖(((1 - t : ℝ)) : ℂ)‖ = |1 - t| from RCLike.norm_ofReal (1 - t),
        show ‖((t : ℝ) : ℂ)‖ = |t| from RCLike.norm_ofReal t,
        abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
    have h2 : (1 - t) * ‖x - T * Complex.I‖ + t * ‖y - T * Complex.I‖ ≤ ρ - R₂ := by
      have h3 : (1 - t) * ‖x - T * Complex.I‖ ≤ (1 - t) * (ρ - R₂) :=
        mul_le_mul_of_nonneg_left hx (by linarith [ht.2])
      have h4 : t * ‖y - T * Complex.I‖ ≤ t * (ρ - R₂) :=
        mul_le_mul_of_nonneg_left hy ht.1
      have h5 : (1 - t) * (ρ - R₂) + t * (ρ - R₂) = ρ - R₂ := by ring
      linarith [h3, h4, h5]
    have h6 : z - T * Complex.I
        = (z - ((1 - t) * x + t * y)) + ((1 - t) * x + t * y - T * Complex.I) := by ring
    rw [h6]
    linarith [norm_add_le (z - ((1 - t) * x + t * y))
      ((1 - t) * x + t * y - T * Complex.I), h1, h2, hz]
  · intro z hz
    refine hmem z (le_of_lt ?_)
    rw [Metric.mem_ball, dist_eq_norm] at hz
    linarith

/-- **The residual at a fixed height.**  With `ς` a gate preimage of `W`, `Z = Xc d W` the curve
point (so `τ₀ Z = d.φ W` and `d.Φ (τ₀ Z) = d.E W`), the pin of `Φp` at `Z`, the pinning `(RIG)` of the
gate coordinate `Φm` at `Z`, and both points in the waist disc where `‖deriv Φm - 1‖ ≤ 1/2`, the
residual `‖Φp ς - d.E W‖` is bounded by `εp + Clip · (2 εp)`. -/
theorem hres_point {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ξ T B R₂ : ℝ} {α : ℂ} {F Φm Φp : ℂ → ℂ} {W ς Z : ℂ} {εp δ Clip : ℝ}
    (hεp : 0 < εp) (hClip : 0 ≤ Clip) (hBpos : 0 < B)
    (hΦm : MandelDim.IsFatouCoordOn F Φm (Work.Pert.Qm Ξ α))
    (hΦmdiff : DifferentiableOn ℂ Φm (Work.Pert.Qm Ξ α))
    (hballQm : Metric.ball (T * Complex.I) B ⊆ Work.Pert.Qm Ξ α)
    (hderB : ∀ v ∈ Metric.ball (T * Complex.I) B, ‖deriv Φm v - 1‖ ≤ 1 / 2)
    (hςB : ς ∈ Metric.ball (T * Complex.I) B) (hZB : Z ∈ Metric.ball (T * Complex.I) B)
    (hςQ : ς ∈ Work.Pert.Qm Ξ α)
    (hΦς : Φm ς = W) (hΦZ : ‖Φm Z - W‖ < εp)
    (hpin : ‖Φp Z - d.Φ (MandelDim.tau0 Z)‖ < εp)
    (hZtau : MandelDim.tau0 Z = d.φ W)
    (hLip : ‖Φp ς - Φp Z‖ ≤ Clip * ‖ς - Z‖)
    (harith : εp + Clip * (2 * εp) < δ) :
    ‖Φp ς - d.E W‖ < δ := by
  -- the waist disc is convex and the derivative is close to `1` on it
  have hconv : ∀ z ∈ Metric.ball (T * Complex.I) B, ∀ z' ∈ Metric.ball (T * Complex.I) B,
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ((1 - t) • z + t • z') ∈ Metric.ball (T * Complex.I) B := by
    intro z hz z' hz' t ht
    exact (convex_ball (T * Complex.I) B) hz hz' (by linarith [ht.2]) ht.1 (by ring)
  have hdiffQ : DifferentiableOn ℂ Φm (Metric.ball (T * Complex.I) B) := hΦmdiff.mono hballQm
  have hanti : ‖ς - Z‖ ≤ 2 * ‖Φm ς - Φm Z‖ :=
    norm_sub_le_two_mul_of_deriv_sub_one (Φ := Φm) (Q := Metric.ball (T * Complex.I) B)
      hconv hdiffQ hderB hςB hZB
  have h2 : ‖ς - Z‖ ≤ 2 * εp := by
    have h3 : ‖Φm ς - Φm Z‖ = ‖W - Φm Z‖ := by rw [hΦς]
    have h4 : ‖W - Φm Z‖ = ‖Φm Z - W‖ := norm_sub_rev _ _
    rw [h3, h4] at hanti
    linarith [hanti, hΦZ]
  -- the pin at `Z`, transported to `ς`
  have hpin' : ‖Φp Z - d.E W‖ < εp := by
    have h := hpin
    rw [hZtau] at h
    simpa [MandelDim.ParabData.E] using h
  calc ‖Φp ς - d.E W‖
      ≤ ‖Φp ς - Φp Z‖ + ‖Φp Z - d.E W‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < Clip * (2 * εp) + εp := by
        have := mul_le_mul_of_nonneg_left h2 hClip
        linarith
    _ < δ := by linarith

end

end Work.Pert.pert2v2
