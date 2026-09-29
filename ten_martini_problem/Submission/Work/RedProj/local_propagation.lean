import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local propagation of smallness for bounded holomorphic functions

If a holomorphic function `g` is bounded by `1` on a ball `B(w,R)` and is exponentially small
`‖g‖ ≤ exp(-s)` on the concentric smaller ball `B(w,ρ)`, then it is small `‖g‖ ≤ exp(-s/2)` on the
concentric ball `B(w,2ρ)`, provided `4ρ < R`.

This is the "two circle" version of the maximum principle: it is proved with Hadamard's three-lines
theorem applied to the pullback `w ↦ g (exp w)` of `g` to the vertical strip
`Real.log ρ ≤ Re w ≤ Real.log (4ρ)`.  On the left edge of the strip `‖g‖ ≤ exp(-s)`, on the right
edge `‖g‖ ≤ 1`, and the midline `Re w = Real.log (2ρ)` is the geometric mean of the two edges.
-/

namespace Work.RedProj

open Set Complex Metric HadamardThreeLines

/-- The ball `B(0, 2ρ)` case of `local_propagation`. -/
private theorem local_propagation_zero {g : ℂ → ℂ} {ρ R s : ℝ}
    (hρ : 0 < ρ) (hR : 4 * ρ < R)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R))
    (h1 : ∀ z ∈ Metric.ball 0 R, ‖g z‖ ≤ 1)
    (hs : ∀ z ∈ Metric.closedBall 0 ρ, ‖g z‖ ≤ Real.exp (-s)) :
    ∀ z ∈ Metric.closedBall 0 (2 * ρ), ‖g z‖ ≤ Real.exp (-(s / 2)) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rcases le_or_gt s 0 with hs0 | hs0
  · -- `s ≤ 0`: the conclusion is weaker than the global bound `‖g‖ ≤ 1`.
    have hzR : z ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, dist_zero_right]
      have : (2 : ℝ) * ρ < R := by linarith
      linarith
    exact le_trans (h1 z hzR) (Real.one_le_exp (by linarith))
  · -- `0 < s`: pull back to the vertical strip and apply Hadamard three lines.
    set l : ℝ := Real.log ρ with hl
    set u : ℝ := Real.log (4 * ρ) with hu
    have hρ4 : 0 < 4 * ρ := by linarith
    have hul : l < u := by rw [hl, hu]; exact Real.log_lt_log hρ (by linarith)
    set H : ℂ → ℂ := fun w => g (Complex.exp w) with hH

    have hmaps : MapsTo Complex.exp (verticalClosedStrip l u) (Metric.ball 0 R) := by
      intro w hw
      simp only [verticalClosedStrip, mem_preimage, mem_Icc] at hw
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      have h2 : Real.exp w.re ≤ Real.exp u := Real.exp_le_exp.mpr hw.2
      rw [hu, Real.exp_log (by linarith)] at h2
      linarith

    have hHan : AnalyticOnNhd ℂ H (verticalClosedStrip l u) := by
      have := AnalyticOnNhd.comp (g := g) (f := Complex.exp)
        (s := verticalClosedStrip l u) (t := Metric.ball 0 R) hg
        (analyticOnNhd_cexp.mono (subset_univ _)) hmaps
      simpa [hH, Function.comp_def] using this

    have hsub : closure (verticalStrip l u) ⊆ verticalClosedStrip l u := by
      have h1' := Complex.continuous_re.closure_preimage_subset (Ioo l u)
      rw [closure_Ioo (ne_of_lt hul)] at h1'
      simpa [verticalStrip, verticalClosedStrip] using h1'

    have hd : DiffContOnCl ℂ H (verticalStrip l u) := by
      refine ⟨hHan.differentiableOn.mono ?_, hHan.continuousOn.mono hsub⟩
      intro w hw
      simp only [verticalStrip, mem_preimage, mem_Ioo] at hw
      simp only [verticalClosedStrip, mem_preimage, mem_Icc]
      exact ⟨le_of_lt hw.1, le_of_lt hw.2⟩

    have hB : BddAbove ((fun w => ‖H w‖) '' verticalClosedStrip l u) := by
      refine bddAbove_def.mpr ⟨1, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      apply h1
      simp only [verticalClosedStrip, mem_preimage, mem_Icc] at hw
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      have h2 : Real.exp w.re ≤ Real.exp u := Real.exp_le_exp.mpr hw.2
      rw [hu, Real.exp_log (by linarith)] at h2
      linarith

    have ha : ∀ w ∈ re ⁻¹' {l}, ‖H w‖ ≤ Real.exp (-s) := by
      intro w hw
      simp only [mem_preimage, mem_singleton_iff] at hw
      apply hs
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp, hw, hl, Real.exp_log hρ]

    have hb : ∀ w ∈ re ⁻¹' {u}, ‖H w‖ ≤ 1 := by
      intro w hw
      simp only [mem_preimage, mem_singleton_iff] at hw
      apply h1
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp, hw, hu, Real.exp_log (by linarith)]
      linarith

    rcases le_or_gt ‖z‖ ρ with hzρ | hzρ
    · -- `‖z‖ ≤ ρ`: use the hypothesis directly.
      have hzc : z ∈ Metric.closedBall 0 ρ := by rwa [Metric.mem_closedBall, dist_zero_right]
      calc ‖g z‖ ≤ Real.exp (-s) := hs z hzc
        _ ≤ Real.exp (-(s / 2)) := Real.exp_le_exp.mpr (by linarith)
    · -- `ρ < ‖z‖ ≤ 2ρ`: pick a preimage under `exp` inside the strip.
      have hz0 : z ≠ 0 := by
        intro h; rw [h] at hzρ; simp at hzρ; linarith
      set w : ℂ := Complex.log z with hw
      have hwexp : Complex.exp w = z := by rw [hw]; exact Complex.exp_log hz0
      have hwre : w.re = Real.log ‖z‖ := by rw [hw]; exact Complex.log_re z
      have hwmem : w ∈ verticalClosedStrip l u := by
        simp only [verticalClosedStrip, mem_preimage, mem_Icc]
        rw [hwre]
        exact ⟨Real.log_le_log hρ (le_of_lt hzρ),
          Real.log_le_log (lt_trans hρ hzρ) (by linarith)⟩
      set τ : ℝ := (w.re - l) / (u - l) with hτ
      have hbound := norm_le_interp_of_mem_verticalClosedStrip' hul hwmem hd hB ha hb
      have hgw : ‖H w‖ = ‖g z‖ := by simp [hH, hwexp]
      rw [← hgw]
      -- The exponent `τ` of the interpolated bound is at most `1/2` because `‖z‖ ≤ 2ρ`.
      have hlog2 : 2 * Real.log ‖z‖ ≤ u + l := by
        have h1' : (2 : ℝ) * Real.log ‖z‖ = Real.log (‖z‖ ^ 2) := by
          rw [Real.log_pow]; norm_num
        have h2' : u + l = Real.log ((2 * ρ) ^ 2) := by
          rw [hu, hl, ← Real.log_mul (show (4 : ℝ) * ρ ≠ 0 by linarith) (ne_of_gt hρ)]
          congr 1; ring
        rw [h1', h2']
        apply Real.log_le_log
        · positivity
        · nlinarith [hz, hρ, norm_nonneg z]
      have hτle : τ ≤ 1 / 2 := by
        rw [hτ, div_le_iff₀ (by linarith : (0 : ℝ) < u - l)]
        linarith [hlog2, hwre]
      calc ‖H w‖ ≤ Real.exp (-s) ^ (1 - τ) * 1 ^ τ := hbound
        _ = Real.exp (-s * (1 - τ)) := by rw [Real.one_rpow, mul_one, ← Real.exp_mul]
        _ ≤ Real.exp (-(s / 2)) := by
            apply Real.exp_le_exp.mpr
            nlinarith [hτle, hs0]

theorem local_propagation {g : ℂ → ℂ} {w : ℂ} {ρ R s : ℝ}
    (hρ : 0 < ρ) (hR : 4 * ρ < R)
    (hg : AnalyticOnNhd ℂ g (Metric.ball w R))
    (h1 : ∀ z ∈ Metric.ball w R, ‖g z‖ ≤ 1)
    (hs : ∀ z ∈ Metric.closedBall w ρ, ‖g z‖ ≤ Real.exp (-s)) :
    ∀ z ∈ Metric.closedBall w (2 * ρ), ‖g z‖ ≤ Real.exp (-(s / 2)) := by
  -- Translate the centre `w` to the origin.
  have hshift : AnalyticOnNhd ℂ (fun z : ℂ => w + z) (Metric.ball 0 R) := by
    have h := (analyticOnNhd_const (v := w) :
      AnalyticOnNhd ℂ (fun _ : ℂ => w) (Metric.ball 0 R)).add
      (analyticOnNhd_id : AnalyticOnNhd ℂ (fun z : ℂ => z) (Metric.ball 0 R))
    convert h using 1
  have hmaps : MapsTo (fun z : ℂ => w + z) (Metric.ball 0 R) (Metric.ball w R) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hz
  have hF_an : AnalyticOnNhd ℂ (fun z => g (w + z)) (Metric.ball 0 R) := by
    have := AnalyticOnNhd.comp (g := g) (f := fun z : ℂ => w + z)
      (s := Metric.ball 0 R) (t := Metric.ball w R) hg hshift hmaps
    simpa [Function.comp_def] using this
  have hF1 : ∀ z ∈ Metric.ball 0 R, ‖g (w + z)‖ ≤ 1 := by
    intro z hz; exact h1 (w + z) (hmaps hz)
  have hFs : ∀ z ∈ Metric.closedBall 0 ρ, ‖g (w + z)‖ ≤ Real.exp (-s) := by
    intro z hz
    apply hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    simpa using hz
  have key := local_propagation_zero hρ hR hF_an hF1 hFs
  intro z hz
  have hz' : z - w ∈ Metric.closedBall 0 (2 * ρ) := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    simpa using hz
  have := key (z - w) hz'
  rwa [show w + (z - w) = z by ring] at this

end Work.RedProj
