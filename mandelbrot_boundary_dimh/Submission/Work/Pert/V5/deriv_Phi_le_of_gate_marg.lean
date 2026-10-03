import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.deriv_le_of_value_gap_explicit

-- the datum hypotheses of the statement are not used by the proof (see the module docstring)
set_option linter.unusedVariables false

/-!
# `Work.Pert.V5.deriv_Phi_le_of_gate_marg`

A **data-independent, `C₂`-free** bound on the derivative of a Fatou coordinate of the perturbed
near-translation `F = liftF u σ α` on the gate `Qm Ξ α = Qreg (Ξ - 1/α) (-Ξ)`:

if the gate margin `min (mgA Ξ α z) (mgB Ξ z)` at `z ∈ Qm Ξ α` is at least `3/2`, then
`‖deriv Φm z‖ ≤ 1024`, for *every* Fatou coordinate `Φm` of `F` on the gate.

This is the tool `NOTES_corridor_left_wk.md` (`norm_deriv_Phi_le_of_marg`, "Koebe value-gap")
asked for: it is the only statement in the area that bounds `Φ'` without the Koebe constant `C₂`,
hence the only one that survives in the doubly-exponential corner of `PertData`.

## The argument

* `min (mgA) (mgB) ≥ 3/2` gives `z ∈ Qm` and, by `ball_in_gate`, the ball
  `ball z ρ ⊆ Qm Ξ α` for `ρ = min (mgA Ξ α z) (mgB Ξ z) / √2 ≥ 3/(2√2) > 33/32`;
* the near-translation bound `‖F z - (z+1)‖ ≤ 1/32` gives `‖F z - z‖ ∈ [31/32, 33/32]`, so
  `a := F z` is a point of the ball with `Φm a = Φm z + 1` (`IsFatouCoordOn`'s Abel relation) at
  distance at least `3/4` from `z`;
* the value-gap estimate with an explicit constant
  (`Work.Pert.V5.deriv_le_of_value_gap_explicit`, via Landau's theorem with the constant `1/100`
  and the weak Koebe one-quarter inequality) gives `‖deriv Φm z‖ ≤ 400π/3 ≤ 1024`.

Note that none of the datum hypotheses (`Ξ`, `rr`, `M`, `α`, `σ`, `u` and their bounds) is used:
the statement is a statement about *any* near-translation and *any* Fatou coordinate of it.
-/

namespace Work.Pert.V5

open Set Metric Filter

noncomputable section

/-- **Forward invariance of the gate under a `33/32`-perturbation, at margin `≥ 3/2`.**

`mgA` and `mgB` are `√2`-Lipschitz (they are `±Re` plus the absolute value of a translate of `Im`),
so along a step of length `≤ 33/32` a margin `≥ 3/2` can drop by at most `√2 · 33/32 < 3/2`.

Equivalently: `ball z (min (mgA Ξ α z) (mgB Ξ z) / √2) ⊆ Qm Ξ α` (`ball_in_gate`) and
`33/32 < 3/(2√2) ≤ min (mgA Ξ α z) (mgB Ξ z) / √2`. -/
theorem mem_Qm_of_margin_close {Ξ : ℝ} {α : ℂ} {z w : ℂ}
    (hm : (3 : ℝ) / 2 ≤ min (mgA Ξ α z) (mgB Ξ z))
    (hw : ‖w - z‖ ≤ 33 / 32) : w ∈ Work.Pert.Qm Ξ α := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hzQ : z ∈ Work.Pert.Qm Ξ α := by
    rw [Work.Pert.V5.mem_Qm_iff_mg]
    exact ⟨lt_of_lt_of_le (by norm_num) (le_trans hm (min_le_left _ _)),
      lt_of_lt_of_le (by norm_num) (le_trans hm (min_le_right _ _))⟩
  refine Work.Pert.V5.ball_in_gate hzQ ?_
  rw [Metric.mem_ball, dist_eq_norm]
  -- `33/32 < 3/(2√2) ≤ min (mgA) (mgB) / √2`
  have hgt : (33 : ℝ) / 32 < (3 : ℝ) / 2 / Real.sqrt 2 := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 32) hs2]
    have hs : Real.sqrt 2 < 16 / 11 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 16 / 11)]
      norm_num
    nlinarith [hs]
  have hle : (3 : ℝ) / 2 / Real.sqrt 2 ≤ min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2 :=
    div_le_div_of_nonneg_right hm hs2.le
  linarith [hw, hle, hgt]

theorem deriv_Phi_le_of_gate_marg {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z : ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hmarg : (3 : ℝ) / 2 ≤ min (Work.Pert.V5.mgA Ξ α z) (Work.Pert.V5.mgB Ξ z)) :
    ‖deriv Φm z‖ ≤ 1024 := by
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  -- ## the displacement `F z - z` is within `1/32` of `1`
  have hFclose : ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32 := (hNT.1.2 z hz).1
  have hdub : ‖Work.Pert.liftF u σ α z - z‖ ≤ 33 / 32 := by
    have h : ‖Work.Pert.liftF u σ α z - z‖
        ≤ ‖Work.Pert.liftF u σ α z - (z + 1)‖ + ‖(1 : ℂ)‖ := by
      have he : Work.Pert.liftF u σ α z - z
          = (Work.Pert.liftF u σ α z - (z + 1)) + 1 := by ring
      rw [he]; exact norm_add_le _ _
    rw [norm_one] at h; linarith
  have hdlb : (31 : ℝ) / 32 ≤ ‖Work.Pert.liftF u σ α z - z‖ := by
    have h := norm_add_le (Work.Pert.liftF u σ α z - z) (1 - (Work.Pert.liftF u σ α z - z))
    have he : (Work.Pert.liftF u σ α z - z) + (1 - (Work.Pert.liftF u σ α z - z)) = (1 : ℂ) := by
      ring
    rw [he, norm_one] at h
    have h2 : ‖1 - (Work.Pert.liftF u σ α z - z)‖ ≤ 1 / 32 := by
      rw [norm_sub_rev]
      have he2 : (Work.Pert.liftF u σ α z - z) - 1 = Work.Pert.liftF u σ α z - (z + 1) := by ring
      rw [he2]; exact hFclose
    linarith
  -- ## the gap point `a := F z` lies in the gate, with the Abel value `Φm z + 1`
  have hFQ : Work.Pert.liftF u σ α z ∈ Work.Pert.Qm Ξ α := mem_Qm_of_margin_close hmarg hdub
  have hval : Φm (Work.Pert.liftF u σ α z) = Φm z + 1 := hΦm.2.2 z hz hFQ
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hρge : (3 : ℝ) / 4 ≤ min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2 := by
    have h1 : (3 : ℝ) / 2 / Real.sqrt 2 ≤ min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2 :=
      div_le_div_of_nonneg_right hmarg hs2.le
    have h2 : (3 : ℝ) / 4 ≤ (3 : ℝ) / 2 / Real.sqrt 2 := by
      rw [le_div_iff₀ hs2]
      have hs : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      nlinarith [hs]
    linarith
  have hρgt : (33 : ℝ) / 32 < min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2 := by
    have h1 : (3 : ℝ) / 2 / Real.sqrt 2 ≤ min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2 :=
      div_le_div_of_nonneg_right hmarg hs2.le
    have h2 : (33 : ℝ) / 32 < (3 : ℝ) / 2 / Real.sqrt 2 := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 32) hs2]
      have hs : Real.sqrt 2 < 16 / 11 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 16 / 11)]
        norm_num
      nlinarith [hs]
    linarith
  have hball : Metric.ball z (min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2) ⊆ Work.Pert.Qm Ξ α :=
    Work.Pert.V5.ball_in_gate hz
  have ha : Work.Pert.liftF u σ α z ∈ Metric.ball z (min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2) := by
    rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hdub hρgt
  -- ## the value-gap estimate
  have hana : ∀ w ∈ Metric.ball z (min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2),
      AnalyticAt ℂ Φm w :=
    fun w hw => (hΦm.1.analyticOnNhd hQopen) w (hball hw)
  have hinj : Set.InjOn Φm (Metric.ball z (min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2)) :=
    hΦm.2.1.mono hball
  have hmain : ‖deriv Φm z‖ ≤ 400 * Real.pi / 3 :=
    Work.Pert.V5.deriv_le_of_value_gap_explicit hρge hana hinj ha hval (by linarith [hdlb])
  have hpi : 400 * Real.pi / 3 ≤ 1024 := by
    have h4 := Real.pi_lt_four
    linarith
  linarith

end

end Work.Pert.V5
