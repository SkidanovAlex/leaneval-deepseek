import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.IntervalCases
import Submission.Work.R1G.GTest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Filter Topology
open scoped Topology

namespace Work.R1G

/-- A degree-two polynomial in `z` times `e^{-z}` decays to `0` at `+∞`, with an
arbitrary overall constant factor `K`.  This is the elementary analytic input behind
`gTest_decayInZ`: every relevant derivative of `gTest ε` is of this shape in the `z`
variable at a fixed angle. -/
theorem tendsto_quad_exp_mul (K a b c : ℝ) :
    Tendsto (fun z : ℝ => K * ((a + b * z + c * z ^ 2) * Real.exp (-z))) atTop (𝓝 0) := by
  have h0 := Real.tendsto_exp_neg_atTop_nhds_zero
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hsum : Tendsto (fun z : ℝ =>
      c * (z ^ 2 * Real.exp (-z)) + b * (z ^ 1 * Real.exp (-z)) + a * Real.exp (-z))
      atTop (𝓝 0) := by
    have h := ((h2.const_mul c).add (h1.const_mul b)).add (h0.const_mul a)
    simpa using h
  have hK : Tendsto (fun z : ℝ => K *
      (c * (z ^ 2 * Real.exp (-z)) + b * (z ^ 1 * Real.exp (-z)) + a * Real.exp (-z)))
      atTop (𝓝 0) := by
    simpa using hsum.const_mul K
  refine hK.congr (fun z => ?_)
  ring

theorem gTest_decayInZ (ε : ℝ) : Work.Spaces.DecayInZ 2 (gTest ε) := by
  intro j i hij θ hθ
  have hi : i ≤ 2 := by omega
  interval_cases i
  · have hj : j ≤ 2 := by omega
    interval_cases j
    · -- (i, j) = (0, 0)
      simp only [Work.Spaces.pzIter_zero, Work.Spaces.pthIter_zero]
      refine (tendsto_quad_exp_mul (ε * gPsi θ) 0 0 1).congr (fun z => ?_)
      simp only [gTest_apply, gPhi]; ring
    · -- (i, j) = (0, 1)
      rw [Work.Spaces.pthIter_zero, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, pz_gTest]
      refine (tendsto_quad_exp_mul (ε * gPsi θ) 0 2 (-1)).congr (fun z => ?_)
      simp only [gPhi1]; ring
    · -- (i, j) = (0, 2)
      rw [Work.Spaces.pthIter_zero, pzIter_two_gTest]
      refine (tendsto_quad_exp_mul (ε * gPsi θ) 2 (-4) 1).congr (fun z => ?_)
      simp only [gPhi2]; ring
  · have hj : j ≤ 1 := by omega
    interval_cases j
    · -- (i, j) = (1, 0)
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, pth_gTest]
      refine (tendsto_quad_exp_mul (ε * gPsi1 θ) 0 0 1).congr (fun z => ?_)
      simp only [Work.Spaces.pzIter_zero, gPhi]; ring
    · -- (i, j) = (1, 1)
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
        Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, pz_pth_gTest]
      refine (tendsto_quad_exp_mul (ε * gPsi1 θ) 0 2 (-1)).congr (fun z => ?_)
      simp only [gPhi1]; ring
  · have hj : j ≤ 0 := by omega
    interval_cases j
    · -- (i, j) = (2, 0)
      rw [pthIter_two_gTest]
      refine (tendsto_quad_exp_mul (ε * gPsi2 θ) 0 0 1).congr (fun z => ?_)
      simp only [Work.Spaces.pzIter_zero, gPhi]; ring

end Work.R1G
