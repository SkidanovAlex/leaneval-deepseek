import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.Jacobian
import Submission.Work.FTS.StrongEps.Jeps_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Transport of an a.e. statement along the log-shift.**  If a property holds for a.e. `w > 0`,
then it holds for `P (z * exp (-p.1))` for a.e. `p : ℝ × ℝ`, for every `z > 0`.

Route: reduce to the one-dimensional statement that `{p₁ | z * exp (-p₁) ∈ N}` is null for a null
set `N ⊆ (0,∞)` — the map `p₁ ↦ z exp (-p₁)` is the inverse of the differentiable bijection
`w ↦ log z - log w` on `(0,∞)`, so the image of a null set is null by
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`; then bound the bad set in `ℝ²` by
`{p₁ | z exp (-p₁) ∈ N} ×ˢ Set.univ` and use `MeasureTheory.Measure.prod_apply` together with
`MeasureTheory.Measure.volume_eq_prod ℝ ℝ`.
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem AEShiftPreimage {z : ℝ} (hz : 0 < z) {P : ℝ → Prop}
    (h : ∀ᵐ w ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), P w) :
    ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)), P (z * Real.exp (-p.1)) := by
  classical
  -- The bad set on `(0,∞)`, which is null.
  set N : Set ℝ := {w | ¬ P w} ∩ Set.Ioi 0 with hN
  have hNvol : volume N = 0 := by
    have h' := (MeasureTheory.ae_iff).mp h
    rwa [Measure.restrict_apply' measurableSet_Ioi] at h'
  -- Members of `N` are exactly the `z * exp (-p.1)` with `¬ P` at them.
  have hTN : ∀ p : ℝ × ℝ, (z * Real.exp (-p.1) ∈ N ↔ ¬ P (z * Real.exp (-p.1))) := by
    intro p
    rw [hN]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, mul_pos hz (Real.exp_pos _)⟩⟩
  -- Its preimage `T` under the shift.
  set T : Set ℝ := {p₁ | z * Real.exp (-p₁) ∈ N} with hT
  have hTvol : volume T = 0 := by
    -- `T` is the image of the null set `N` under the differentiable map `log z - log ·`.
    have himg : T = (fun w => Real.log z - Real.log w) '' N := by
      ext p
      rw [hT]
      constructor
      · intro hp
        have hlog : Real.log (z * Real.exp (-p)) = Real.log z - p := by
          rw [Real.log_mul hz.ne' (Real.exp_ne_zero _), Real.log_exp]
          ring
        refine ⟨z * Real.exp (-p), hp, ?_⟩
        show Real.log z - Real.log (z * Real.exp (-p)) = p
        rw [hlog]; ring
      · rintro ⟨w, hw, rfl⟩
        change z * Real.exp (-(Real.log z - Real.log w)) ∈ N
        have hwpos : 0 < w := by rw [hN] at hw; exact hw.2
        have harg : -(Real.log z - Real.log w) = Real.log w - Real.log z := by ring
        have hexp : Real.exp (Real.log w - Real.log z) = w / z := by
          rw [Real.exp_sub, Real.exp_log hwpos, Real.exp_log hz]
        rw [harg, hexp, mul_div_cancel₀ w hz.ne']
        exact hw
    rw [himg]
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hNvol
    intro w hw
    rw [hN] at hw
    exact ((Real.differentiableAt_log (hw.2 : 0 < w).ne').const_sub
      (Real.log z)).differentiableWithinAt
  -- Conclude from `volume T = 0` by Fubini.
  rw [MeasureTheory.ae_iff]
  have hset : {p : ℝ × ℝ | ¬ P (z * Real.exp (-p.1))} = T ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_prod, Set.mem_univ, and_true, hT, Set.mem_ofPred_eq]
    exact (hTN p).symm
  rw [hset, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, hTvol]
  simp

end Work.FTS.StrongEps.EpsLocalPStar
