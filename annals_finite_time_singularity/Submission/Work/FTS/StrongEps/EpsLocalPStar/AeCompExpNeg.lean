import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.Jacobian
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

theorem AeCompExpNeg {P : ℝ → Prop} {z ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (h : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), P u) :
    ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), P (z * Real.exp (-(ε * p))) := by
  classical
  -- The bad set on `(0,∞)`, which is null by the hypothesis.
  set N : Set ℝ := {w | ¬ P w} ∩ Set.Ioi 0 with hN
  have hNvol : volume N = 0 := by
    have h' := (MeasureTheory.ae_iff).mp h
    rwa [Measure.restrict_apply' measurableSet_Ioi] at h'
  -- Membership in `N` is exactly failure of `P` at `z * exp (-(ε p))`.
  have hTN : ∀ p : ℝ, (z * Real.exp (-(ε * p)) ∈ N ↔ ¬ P (z * Real.exp (-(ε * p)))) := by
    intro p
    rw [hN]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, mul_pos hz (Real.exp_pos _)⟩⟩
  -- Its preimage `T` under the map `p ↦ z * exp (-(ε p))`.
  set T : Set ℝ := {p | z * Real.exp (-(ε * p)) ∈ N} with hT
  have hTvol : volume T = 0 := by
    -- `T` is the image of the null set `N` under the differentiable map
    -- `w ↦ (log z - log w) / ε`, the inverse of `p ↦ z exp (-(ε p))`.
    have himg : T = (fun w => (Real.log z - Real.log w) / ε) '' N := by
      ext p
      rw [hT]
      constructor
      · intro hp
        refine ⟨z * Real.exp (-(ε * p)), hp, ?_⟩
        have hlog : Real.log (z * Real.exp (-(ε * p))) = Real.log z - ε * p := by
          rw [Real.log_mul hz.ne' (Real.exp_ne_zero _), Real.log_exp]
          ring
        show (Real.log z - Real.log (z * Real.exp (-(ε * p)))) / ε = p
        rw [hlog]
        field_simp
        ring
      · rintro ⟨w, hw, rfl⟩
        change z * Real.exp (-(ε * ((Real.log z - Real.log w) / ε))) ∈ N
        have hwpos : 0 < w := by rw [hN] at hw; exact hw.2
        have harg : -(ε * ((Real.log z - Real.log w) / ε)) = Real.log w - Real.log z := by
          field_simp
          ring
        have hexp : Real.exp (Real.log w - Real.log z) = w / z := by
          rw [Real.exp_sub, Real.exp_log hwpos, Real.exp_log hz]
        rw [harg, hexp, mul_div_cancel₀ w hz.ne']
        exact hw
    rw [himg]
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hNvol
    intro w hw
    rw [hN] at hw
    exact (((Real.differentiableAt_log (hw.2 : 0 < w).ne').const_sub (Real.log z)).div_const
      ε).differentiableWithinAt
  -- Conclude.
  rw [MeasureTheory.ae_iff]
  have hset : {p : ℝ | ¬ P (z * Real.exp (-(ε * p)))} = T := by
    ext p
    simp only [hT, Set.mem_ofPred_eq]
    exact (hTN p).symm
  rw [hset, hTvol]

end Work.FTS.StrongEps.EpsLocalPStar
