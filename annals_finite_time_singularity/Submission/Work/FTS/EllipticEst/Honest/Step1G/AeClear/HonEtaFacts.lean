import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The angular weight `σ = sin(2θ)^{-η}` on the slices

Two facts about `σ`, copied from `Honest/HonEnergy.lean` (which cannot be imported here: that
module imports `Step1G/EnergyG.lean`, so importing it from the `EnergyG` cone would create a
module cycle).  They are the only two declarations of that module used by the `Ae`-energy chain
(`AngAWeak/aeEnergyWAux.lean`), which is re-routed through the clean copies in this directory. -/

/-- `σ = sin(2θ)^{-η}` is `≥ 1` on the open angular interval. -/
theorem one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_ <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hl : Real.log (Real.sin (2 * θ)) ≤ 0 := Real.log_nonpos hs.le hs1
  have hmain : (0 : ℝ) ≤ Real.log (Real.sin (2 * θ)) * (-(Work.Spaces.eta)) := by
    have h := mul_nonpos_of_nonpos_of_nonneg hl hη0
    nlinarith [h]
  have h := Real.exp_le_exp.mpr hmain
  rw [Work.FTS.EllipticEst.sEta, Real.rpow_def_of_pos hs]
  simpa only [Real.exp_zero] using h

/-- Almost every point of `Iθ` (for the restricted measure) lies in the *open* interval: the two
endpoints are a null set. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, ae_iff]
  refine measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    simp only [Set.mem_setOf_eq, not_imp] at hθ
    obtain ⟨hθI, hne⟩ := hθ
    rcases eq_or_lt_of_le (Set.mem_Icc.mp hθI).1 with h | h
    · exact Or.inl h.symm
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθI).2 with h2 | h2
      · exact Or.inr h2
      · exact absurd ⟨h, h2⟩ hne
  · have : ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [this]
    exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))

end Work.FTS.EllipticEst.Honest
