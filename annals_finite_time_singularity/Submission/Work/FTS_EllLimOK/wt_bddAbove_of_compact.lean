/-
Copyright: work module for the Elgindi finite-time singularity project.

# Boundedness of the growth weight `wt` on compact subsets of the open quadrant

`Work.FTS_EllLimOK.wt z θ = (1 + 1/z + 1/(θ(π/2-θ))) / (1+z)` is the growth weight of the
`Closed.LocalBound` workstream.  It is *continuous on the open quadrant*
`Work.FTS.EllipticEst.Q0 = (0,∞) × (0,π/2)` (all the denominators are non-zero there — the two
potential blow-up factors `1/z`, `1/(θ(π/2-θ))` and the factor `1/(1+z)` are safe), and so is the
augmented weight

`wt z θ * (1/z + 1/sin(2θ))`

(the only new denominator is `sin(2θ)`, which is positive for `0 < θ < π/2`).

Hence both are bounded above on any compact subset `K` of the open quadrant: the image of a
compact set under a continuous map is compact, and a compact subset of `ℝ` is bounded above.

This module is complete: every declaration below is fully proved.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.LimDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

open Set MeasureTheory

/-! ## Non-vanishing of the denominators on the open quadrant -/

private lemma z_ne_zero_of_mem_Q0 {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    p.1 ≠ 0 :=
  ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1

private lemma th_mul_ne_zero_of_mem_Q0 {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    p.2 * (Real.pi / 2 - p.2) ≠ 0 := by
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (mul_pos h0 (by linarith [Real.pi_pos]))

private lemma sin_two_ne_zero_of_mem_Q0 {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Real.sin (2 * p.2) ≠ 0 := by
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-! ## Continuity on the open quadrant -/

/-- The growth weight `wt` is continuous on the open quadrant. -/
lemma continuousOn_wt :
    ContinuousOn (fun p : ℝ × ℝ => wt p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hnum : ContinuousOn (fun p : ℝ × ℝ => 1 + 1 / p.1 + 1 / (p.2 * (Real.pi / 2 - p.2)))
      Work.FTS.EllipticEst.Q0 :=
    (continuousOn_const.add (continuousOn_const.div continuousOn_fst
        (fun p hp => z_ne_zero_of_mem_Q0 hp))).add
      (continuousOn_const.div
        (continuousOn_snd.mul (continuousOn_const.sub continuousOn_snd))
        (fun p hp => th_mul_ne_zero_of_mem_Q0 hp))
  have hden : ContinuousOn (fun p : ℝ × ℝ => 1 + p.1) Work.FTS.EllipticEst.Q0 :=
    continuousOn_const.add continuousOn_fst
  have h := hnum.div hden (fun p hp => by
    have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1; linarith)
  exact h

/-- The augmented growth weight `wt · (1/z + 1/sin 2θ)` is continuous on the open quadrant. -/
lemma continuousOn_wt_mul :
    ContinuousOn (fun p : ℝ × ℝ => wt p.1 p.2 * (1 / p.1 + 1 / Real.sin (2 * p.2)))
      Work.FTS.EllipticEst.Q0 := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  refine continuousOn_wt.mul ?_
  exact (continuousOn_const.div continuousOn_fst
      (fun p hp => z_ne_zero_of_mem_Q0 hp)).add
    (continuousOn_const.div hsin (fun p hp => sin_two_ne_zero_of_mem_Q0 hp))

/-! ## The main statement -/

theorem wt_bddAbove_of_compact {K : Set (ℝ × ℝ)} (hKc : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ M N : ℝ, (∀ p ∈ K, Work.FTS_EllLimOK.wt p.1 p.2 ≤ M) ∧
      (∀ p ∈ K, Work.FTS_EllLimOK.wt p.1 p.2 * (1 / p.1 + 1 / Real.sin (2 * p.2)) ≤ N) := by
  have hM : ∃ M : ℝ, ∀ p ∈ K, wt p.1 p.2 ≤ M := by
    rcases (hKc.image_of_continuousOn (continuousOn_wt.mono hKQ)).bddAbove with ⟨M, hM⟩
    exact ⟨M, fun p hp => hM ⟨p, hp, rfl⟩⟩
  have hN : ∃ N : ℝ, ∀ p ∈ K,
      wt p.1 p.2 * (1 / p.1 + 1 / Real.sin (2 * p.2)) ≤ N := by
    rcases (hKc.image_of_continuousOn (continuousOn_wt_mul.mono hKQ)).bddAbove with ⟨N, hN⟩
    exact ⟨N, fun p hp => hN ⟨p, hp, rfl⟩⟩
  exact ⟨hM.choose, hN.choose, hM.choose_spec, hN.choose_spec⟩

end Work.FTS_EllLimOK
