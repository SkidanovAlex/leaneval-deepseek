import Mathlib
import Submission.Work.APsi.defs
import Submission.Work.APsi.slitQ_branch
import Submission.Work.APsi.slit_norm_eq_one

/-!
# Area `Ψ_A`: the analytic facts on the slit map `slit r`

`slit r z = ((1+r)^2 - 2(r-1)^2 z + (1+r)^2 z^2 + (1+r)(z-1) √(slitQ r z)) / (8 r z)`
(the principal square root, value `0` at `z = 0`) is the conformal isomorphism
`(𝔻,0) → (𝔻 ∖ (-1,-r], 0)` of Calegari--Dimitrov--Tang (arXiv:2408.15403, eq. `(slit)`).

This module proves the elementary analytic facts needed downstream: continuity on the closed
unit disc, holomorphy on the open unit disc, `slit r 0 = 0`, the disc bounds `‖slit r z‖ ≤ 1`
and `< 1` on the closed/open disc, and zero-freeness off the origin.

The algebraic core (`slit_mul`, `slit_joukowski_ab`, `slit_ne_zero`, …) is in
`Submission.Work.APsi.defs`; the branch analysis of the radicand `slitQ` and the Joukowski
cut-off are the auxiliary modules `slitQ_branch` and `slit_norm_eq_one`.
-/

namespace Work.APsi

open Submission.CDTPlan Complex Metric

noncomputable section

/-! ## Polynomials and the square root of `slitQ` -/

theorem continuous_slitP (r : ℝ) : Continuous (slitP r) := by
  unfold slitP; fun_prop

theorem continuous_slitQ (r : ℝ) : Continuous (slitQ r) := by
  unfold slitQ; fun_prop

theorem differentiable_slitP (r : ℝ) : Differentiable ℂ (slitP r) := by
  unfold slitP; fun_prop

theorem differentiable_slitQ (r : ℝ) : Differentiable ℂ (slitQ r) := by
  unfold slitQ; fun_prop

/-- `z ↦ √(slitQ r z)` is continuous on the closed unit disc: on the closed disc `slitQ r z`
lies in `slitPlane ∪ {0}` and the exponent `1/2` has positive real part, so
`Complex.continuousAt_cpow_const_of_re_pos` applies at every point (including the two zeros of
`slitQ` on the unit circle). -/
theorem continuousOn_slitQ_cpow (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ContinuousOn (fun z : ℂ => (slitQ r z) ^ (1 / 2 : ℂ)) (closedBall 0 1) := by
  intro z hz
  have hzmem : ‖z‖ ≤ 1 := by rwa [mem_closedBall, dist_zero_right] at hz
  have hcond : 0 ≤ (slitQ r z).re ∨ (slitQ r z).im ≠ 0 := by
    rcases (slitQ_branch r hr0 hr1).2 z hzmem with h | h
    · rw [mem_slitPlane_iff] at h; exact h.imp (fun h => le_of_lt h) id
    · rw [h]; simp
  have hw : 0 < (1 / 2 : ℂ).re := by norm_num
  exact (continuousAt_cpow_const_of_re_pos hcond hw).comp_continuousWithinAt
    ((continuous_slitQ r).continuousAt.continuousWithinAt)

/-- `z ↦ √(slitQ r z)` is holomorphic on the open unit disc: `slitQ` maps the open unit disc
into `slitPlane`. -/
theorem differentiableOn_slitQ_cpow (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    DifferentiableOn ℂ (fun z : ℂ => (slitQ r z) ^ (1 / 2 : ℂ)) (ball 0 1) := by
  apply DifferentiableOn.cpow_const
  · exact (differentiable_slitQ r).differentiableOn
  · intro z hz
    exact (slitQ_branch r hr0 hr1).1 z (by rwa [mem_ball, dist_zero_right] at hz)

/-! ## Continuity and holomorphy of `slit r` -/

theorem continuousOn_slitR (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ContinuousOn (slitR r) (closedBall 0 1) := by
  have h1 : ContinuousOn (fun z : ℂ => (1 + (r : ℂ)) * (z - 1)) (closedBall 0 1) :=
    continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
  have h2 : ContinuousOn
      (fun z : ℂ => (1 + (r : ℂ)) * (z - 1) * ((slitQ r z) ^ (1 / 2 : ℂ))) (closedBall 0 1) :=
    h1.mul (continuousOn_slitQ_cpow r hr0 hr1)
  rw [show slitR r = (fun z : ℂ => (1 + (r : ℂ)) * (z - 1) * ((slitQ r z) ^ (1 / 2 : ℂ))) from by
    funext z; simp [slitR]]
  exact h2

theorem differentiableOn_slitR (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    DifferentiableOn ℂ (slitR r) (ball 0 1) := by
  have h1 : DifferentiableOn ℂ (fun z : ℂ => (1 + (r : ℂ)) * (z - 1)) (ball 0 1) :=
    (differentiableOn_const (1 + (r : ℂ))).mul
      (differentiableOn_id.sub (differentiableOn_const (1 : ℂ)))
  have h2 : DifferentiableOn ℂ
      (fun z : ℂ => (1 + (r : ℂ)) * (z - 1) * ((slitQ r z) ^ (1 / 2 : ℂ))) (ball 0 1) :=
    h1.mul (differentiableOn_slitQ_cpow r hr0 hr1)
  rw [show slitR r = (fun z : ℂ => (1 + (r : ℂ)) * (z - 1) * ((slitQ r z) ^ (1 / 2 : ℂ))) from by
    funext z; simp [slitR]]
  exact h2

/-- `slit r` is continuous on the closed unit disc. -/
theorem continuousOn_slit (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ContinuousOn (slit r) (closedBall 0 1) := by
  have hden : ContinuousOn (fun z : ℂ => slitR r z - slitP r z) (closedBall 0 1) :=
    (continuousOn_slitR r hr0 hr1).sub (continuous_slitP r).continuousOn
  have hquot : ContinuousOn (fun z : ℂ => -8 * (r : ℂ) / (slitR r z - slitP r z))
      (closedBall 0 1) :=
    continuousOn_const.div hden (fun z _ => slitRP_ne r hr0 z)
  have h2 : ContinuousOn (fun z : ℂ => z * (-8 * (r : ℂ) / (slitR r z - slitP r z)))
      (closedBall 0 1) := continuousOn_id.mul hquot
  rw [show slit r = (fun z : ℂ => z * (-8 * (r : ℂ) / (slitR r z - slitP r z))) from
    funext (fun z => slit_mul r hr0 z)]
  exact h2

/-- `slit r` is holomorphic on the open unit disc. -/
theorem differentiableOn_slit (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    DifferentiableOn ℂ (slit r) (ball 0 1) := by
  have hden : DifferentiableOn ℂ (fun z : ℂ => slitR r z - slitP r z) (ball 0 1) :=
    (differentiableOn_slitR r hr0 hr1).sub (differentiable_slitP r).differentiableOn
  have hquot : DifferentiableOn ℂ (fun z : ℂ => -8 * (r : ℂ) / (slitR r z - slitP r z))
      (ball 0 1) :=
    (differentiableOn_const (-8 * (r : ℂ))).div hden (fun z _ => slitRP_ne r hr0 z)
  have h2 : DifferentiableOn ℂ (fun z : ℂ => z * (-8 * (r : ℂ) / (slitR r z - slitP r z)))
      (ball 0 1) := differentiableOn_id.mul hquot
  rw [show slit r = (fun z : ℂ => z * (-8 * (r : ℂ) / (slitR r z - slitP r z))) from
    funext (fun z => slit_mul r hr0 z)]
  exact h2

/-! ## Value and modulus bounds -/

theorem slit_zero (r : ℝ) : slit r 0 = 0 := by
  simp [Submission.CDTPlan.slit]

/-- Continuity of the modulus profile `t ↦ ‖slit r (t z)‖` along a segment inside the closed
unit disc. -/
theorem continuousOn_slit_seg (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ContinuousOn (fun t : ℝ => ‖slit r ((t : ℂ) * z)‖) (Set.Icc 0 1) := by
  have hmaps : Set.MapsTo (fun t : ℝ => (t : ℂ) * z) (Set.Icc 0 1) (closedBall 0 1) := by
    intro t ht
    rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
      _ = ‖z‖ := one_mul _
      _ ≤ 1 := hz
  have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) * z) (Set.Icc 0 1) :=
    (Complex.continuous_ofReal.mul continuous_const).continuousOn
  exact ((continuousOn_slit r hr0 hr1).comp h1 hmaps).norm

/-- `‖slit r z‖ < 1` on the open unit disc. -/
theorem slit_norm_lt_one (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ z : ℂ, ‖z‖ < 1 → ‖slit r z‖ < 1 := by
  intro z hz
  let F : ℝ → ℝ := fun t => ‖slit r ((t : ℂ) * z)‖
  have hcont : ContinuousOn F (Set.Icc 0 1) := continuousOn_slit_seg r hr0 hr1 z (le_of_lt hz)
  have hF0 : F 0 = 0 := by simp [F, Submission.CDTPlan.slit]
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t ≠ 1 := by
    intro t ht hFt
    have hw : ‖slit r ((t : ℂ) * z)‖ = 1 := by simpa [F] using hFt
    have hnorm1 : ‖((t : ℂ) * z)‖ = 1 := by
      rcases eq_or_ne ((t : ℂ) * z) 0 with h0 | h0
      · rw [h0] at hw; simp [Submission.CDTPlan.slit] at hw
      · exact slit_norm_eq_one r hr0 hr1 _ hw
    have hlt : ‖((t : ℂ) * z)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
        _ = ‖z‖ := one_mul _
        _ < 1 := hz
    linarith
  rcases lt_or_gt_of_ne (hne 1 (by norm_num)) with h | h
  · simpa [F] using h
  · exfalso
    have hmem : (1 : ℝ) ∈ Set.Icc (F 0) (F 1) := by
      rw [hF0]; exact ⟨zero_le_one, le_of_lt h⟩
    rcases (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcont) hmem with
      ⟨t, ht, hFt⟩
    exact hne t ht hFt

/-- `‖slit r z‖ ≤ 1` on the closed unit disc. -/
theorem slit_norm_le_one (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → ‖slit r z‖ ≤ 1 := by
  intro z hz
  by_contra hcon
  rw [not_le] at hcon
  let F : ℝ → ℝ := fun t => ‖slit r ((t : ℂ) * z)‖
  have hcont : ContinuousOn F (Set.Icc 0 1) := continuousOn_slit_seg r hr0 hr1 z hz
  have hF0 : F 0 = 0 := by simp [F, Submission.CDTPlan.slit]
  have hF1 : F 1 = ‖slit r z‖ := by simp [F]
  have hmem : (1 : ℝ) ∈ Set.Icc (F 0) (F 1) := by
    rw [hF0, hF1]; exact ⟨zero_le_one, le_of_lt hcon⟩
  rcases (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcont) hmem with
    ⟨t, ht, hFt⟩
  have ht1 : t < 1 := by
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact h
    · exfalso; rw [h, hF1] at hFt; linarith
  have htz : ‖((t : ℂ) * z)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖z‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hz ht.1
      _ = t := mul_one _
      _ < 1 := ht1
  have hlt : F t < 1 := slit_norm_lt_one r hr0 hr1 _ htz
  rw [hFt] at hlt
  exact lt_irrefl 1 hlt

/-- `slit r` vanishes only at the origin. -/
theorem slit_eq_zero (r : ℝ) (hr0 : 0 < r) :
    ∀ z : ℂ, slit r z = 0 → z = 0 := by
  intro z hz
  by_contra h
  exact slit_ne_zero r hr0 z h hz

/-! ## Assembly -/

theorem slit_facts (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ContinuousOn (Submission.CDTPlan.slit r) (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ (Submission.CDTPlan.slit r) (Metric.ball 0 1) ∧
      Submission.CDTPlan.slit r 0 = 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖Submission.CDTPlan.slit r z‖ ≤ 1) ∧
      (∀ z : ℂ, ‖z‖ < 1 → ‖Submission.CDTPlan.slit r z‖ < 1) ∧
      (∀ z : ℂ, Submission.CDTPlan.slit r z = 0 → z = 0) :=
  ⟨continuousOn_slit r hr0 hr1, differentiableOn_slit r hr0 hr1, slit_zero r,
    slit_norm_le_one r hr0 hr1, slit_norm_lt_one r hr0 hr1, slit_eq_zero r hr0⟩

end

end Work.APsi
