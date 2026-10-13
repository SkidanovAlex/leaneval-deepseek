/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise bound of the pure `D_z`-summand of the interior product rule

`Work.FTS.H2.HQ.ZsummandQ` assembles the `L²`-bound of the pure `D_z`-slots
`D_z^i (f·g) · w/sin(2θ)^{η/2}` of the `ℋ⁴`-integrand of the product `f·g` for
`f, g` in the interior class `SmoothQuad` with the pointwise `L^∞`-packages
`PwBd α f Cf`, `PwBd α g Cg`.

This file contains the *pointwise* ingredient of that assembly: Leibniz
(`DzIter_mul_quad`) expands `D_z^i (f·g)` into `∑_{b≤i} C(i,b) D_z^b f · D_z^{i-b} g`;
for each `b` one of the two factors has `D_z`-order `≤ 2` (namely `D_z^b f` if
`b ≤ 2`, and `D_z^{i-b} g` otherwise, since `i ≤ 4`) and is bounded pointwise by
`PwBd` (`|mixed b 0 f| ≤ √(Cf/(γ-1)·|f|²_{ℋ⁴})`), while the other factor keeps
the light weight `w/sin(2θ)^{η/2}` and is the summand `zsFbQ` of the majorant
`zsVQ`.  The triangle inequality for the finite sum concludes.

This is the `PwBd`/`SmoothQuad` counterpart of the pointwise step of
`Work.Spaces.HProductRule_Zsummand` (which uses `SmoothNbhd` and the fixed
constant `100`).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.HQ.ZsummandQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-- **The pointwise bound of the pure `D_z`-summand of the product rule.**

On the open quadrant, the light-weighted `D_z^i`-slot of the product `f·g`
(`i ≤ 4`) is dominated by the majorant `zsVQ`: the Leibniz expansion is split,
each summand keeps its factor of `D_z`-order `> 2` in the light `L²`-weight and
bounds the complementary factor of order `≤ 2` by the `PwBd`-package. -/
theorem ZsummandQPtwise (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i : ℕ) (hi : i ≤ 4)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hPf : Work.FTS.H2.HQ.PwBd α f Cf) (hPg : Work.FTS.H2.HQ.PwBd α g Cg) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        ≤ Work.FTS.H2.HQ.zsVQ α f g Cf Cg i z θ := by
  intro z hzpos θ hθ0 hθ1
  have hz : z ∈ Iz := le_of_lt hzpos
  -- Leibniz expansion of `D_z^i (f·g)` on the open quadrant
  have hL := Work.FTS.H2.HQ.DzIter_mul_quad i f g hf hg z hz θ ⟨hθ0, hθ1⟩
  have hX : DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (DzIter b f z θ * DzIter (i - b) g z θ)
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2)) := by
    rw [hL, Finset.sum_mul]
  rw [hX, zsVQ_apply α f g Cf Cg i z θ]
  -- the triangle inequality for the finite sum
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum (fun b hb => ?_)
  have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  by_cases hb2 : b ≤ 2
  · -- `b ≤ 2`: `D_z^b f` is the factor pulled out pointwise, `D_z^{i-b} g` is kept
    have hbnd : (DzIter b f z θ) ^ 2 ≤ Cf / (gam α - 1) * HkSq α 4 f := by
      have h := hPf.bound b 0 (by omega) z hzpos θ hθ0 hθ1
      simpa only [Work.Spaces.mixed_zero_right] using h
    have habs : |DzIter b f z θ| ≤ Real.sqrt (Cf / (gam α - 1) * HkSq α 4 f) :=
      Real.abs_le_sqrt hbnd
    rw [zsAAQ_mul_zsFbQ_eq α f g Cf Cg i b z θ hb2]
    calc |(i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ)
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|
        = (|(i.choose b : ℝ)| * |DzIter b f z θ|)
            * (|DzIter (i - b) g z θ| * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
          simp only [abs_mul]; ring
      _ ≤ (|(i.choose b : ℝ)| * Real.sqrt (Cf / (gam α - 1) * HkSq α 4 f))
            * (|DzIter (i - b) g z θ| * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left habs (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |(i.choose b : ℝ)| * Real.sqrt (Cf / (gam α - 1) * HkSq α 4 f)
            * |DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
          rw [abs_mul]
  · -- `2 < b ≤ i ≤ 4`, so `i - b ≤ 2`: now `D_z^{i-b} g` is pulled out pointwise
    have hbnd : (DzIter (i - b) g z θ) ^ 2 ≤ Cg / (gam α - 1) * HkSq α 4 g := by
      have h := hPg.bound (i - b) 0 (by omega) z hzpos θ hθ0 hθ1
      simpa only [Work.Spaces.mixed_zero_right] using h
    have habs : |DzIter (i - b) g z θ| ≤ Real.sqrt (Cg / (gam α - 1) * HkSq α 4 g) :=
      Real.abs_le_sqrt hbnd
    rw [zsAAQ_mul_zsFbQ_eq' α f g Cf Cg i b z θ hb2]
    calc |(i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ)
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|
        = (|(i.choose b : ℝ)| * |DzIter b f z θ|)
            * (|DzIter (i - b) g z θ| * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
          simp only [abs_mul]; ring
      _ ≤ (|(i.choose b : ℝ)| * |DzIter b f z θ|)
            * (Real.sqrt (Cg / (gam α - 1) * HkSq α 4 g)
              * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right habs (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |(i.choose b : ℝ)| * Real.sqrt (Cg / (gam α - 1) * HkSq α 4 g)
            * |DzIter b f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
          rw [abs_mul]; ring

end Work.FTS.H2.HQ
