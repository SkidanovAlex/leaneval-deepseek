/-
# `Work.SolutionDelivery.Scaling.Main` — the Euler scaling to unit blow-up time

`Work.SolutionDelivery.eulerScalingToUnitData_holds` is the proof of the corrected scaling input
`EulerScalingToUnitData`: from a solution of the class of `theorem_1` on `[0,T)` with `T > 0`,
blowing up at `T` and with Lichtenstein–Gunther admissible datum, the rescaling
`u'(x,t) = λu(λx,λ²t)`, `p'(x,t) = λ²p(λx,λ²t)`, `u₀'(x) = λu₀(λx)` at `λ = √T` produces a datum
and a solution with all the properties of the challenge at blow-up time `1`.

Each preservation statement is a lemma of this subdirectory:
`div_rescale`, `vorticity_rescale`, `isOdd_rescaleDatum`, `isContDiffHolder_rescaleDatum`,
`vorticityDecay_rescaleDatum`, `bkm_rescale`, `contDiffOn_rescale`, `contDiffOn_rescalePressure`,
`euler_eq_rescale`, `isContDiffHolderOn_rescale`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Scaling.div_rescale
import Submission.Work.SolutionDelivery.Scaling.vorticity_rescale
import Submission.Work.SolutionDelivery.Scaling.isOdd_rescaleDatum
import Submission.Work.SolutionDelivery.Scaling.isContDiffHolder_rescaleDatum
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.SolutionDelivery.Scaling.bkm_rescale
import Submission.Work.SolutionDelivery.Scaling.contDiffOn_rescale
import Submission.Work.SolutionDelivery.Scaling.contDiffOn_rescalePressure
import Submission.Work.SolutionDelivery.Scaling.euler_eq_rescale
import Submission.Work.SolutionDelivery.Scaling.isContDiffHolderOn_rescale

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- **The corrected scaling input, proved.** -/
theorem eulerScalingToUnitData_holds : EulerScalingToUnitData := by
  intro α u₀ T p u hdata hT hsol hodd hstrips hbkm
  set lam : ℝ := Real.sqrt T with hlamdef
  have hlam_pos : 0 < lam := Real.sqrt_pos.mpr hT
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hlam2 : 0 < lam ^ 2 := pow_pos hlam_pos 2
  have hsq : lam ^ 2 = T := Real.sq_sqrt hT.le
  refine ⟨rescaleDatum lam u₀, rescalePressure lam p, rescale lam u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the datum is divergence-free
    funext x
    show FiniteTimeSingularity.div (fun y => lam • u₀ (lam • y)) x = 0
    rw [Scaling.div_rescale (lam := lam) (F := u₀) hlam_ne x,
      congrFun hdata.div_free (lam • x)]
    simp
  · -- the datum is odd
    exact Scaling.isOdd_rescaleDatum hdata.odd
  · -- the datum is `C^{1,α}`
    exact Scaling.isContDiffHolder_rescaleDatum hdata.contDiffHolder
  · -- the vorticity of the datum decays
    exact Scaling.vorticityDecay_rescaleDatum hlam_ne hdata.vort_decay
  · -- oddness at every time
    intro t ht
    have hodd_slice : IsOdd (fun x => u x (lam ^ 2 * t)) := by
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · rw [← h0, mul_zero, hsol.init]
        exact hdata.odd
      · exact hodd (lam ^ 2 * t) ⟨(mul_pos hlam2 h0).le, by
          calc lam ^ 2 * t < lam ^ 2 * 1 := mul_lt_mul_of_pos_left ht.2 hlam2
            _ = lam ^ 2 := mul_one _
            _ = T := hsq⟩
    exact Scaling.isOdd_rescaleDatum hodd_slice
  · -- the rescaled fields solve the Euler equation with datum `u₀'` up to time `1`
    refine ⟨Scaling.contDiffOn_rescale hlam_ne hsq hsol.solContDiff,
      Scaling.contDiffOn_rescalePressure hlam_ne hsq hsol.pressureContDiff, ?_, ?_, ?_⟩
    · -- the equation
      intro x t ht
      refine Scaling.euler_eq_rescale hlam_ne hsq ?_ ?_ hsol.eq x t ht
      · exact hsol.solContDiff.mono (fun z hz => ⟨trivial, ⟨hz.2.1.le, hz.2.2⟩⟩)
      · exact hsol.pressureContDiff.mono (fun z hz => ⟨trivial, ⟨hz.2.1.le, hz.2.2⟩⟩)
    · -- divergence-freeness of the rescaled slices
      intro t ht
      funext x
      show FiniteTimeSingularity.div (fun y => lam • u (lam • y) (lam ^ 2 * t)) x = 0
      rw [Scaling.div_rescale (lam := lam) (F := fun y => u y (lam ^ 2 * t)) hlam_ne x]
      have hmem : lam ^ 2 * t ∈ Set.Ioo 0 T := by
        refine ⟨mul_pos hlam2 ht.1, ?_⟩
        calc lam ^ 2 * t < lam ^ 2 * 1 := mul_lt_mul_of_pos_left ht.2 hlam2
          _ = lam ^ 2 := mul_one _
          _ = T := hsq
      rw [congrFun (hsol.div_free (lam ^ 2 * t) hmem) (lam • x)]
      simp
    · -- the datum of the rescaled solution
      funext x
      show lam • u (lam • x) (lam ^ 2 * 0) = lam • u₀ (lam • x)
      rw [mul_zero, congrFun hsol.init (lam • x)]
  · -- the strip `C^{1,α}` regularity at blow-up time `1`
    intro S hS
    exact Scaling.isContDiffHolderOn_rescale hlam_ne hsq hstrips hS
  · -- the BKM integral diverges at `1`
    have hbkm_rescale : Work.LWP.bkm (rescale lam u)
        = fun t => Work.LWP.bkm u (lam ^ 2 * t) := funext fun t => Scaling.bkm_rescale hlam_ne u t
    rw [hbkm_rescale]
    have hmap : Filter.Tendsto (fun t : ℝ => lam ^ 2 * t) (𝓝[<] (1 : ℝ)) (𝓝[<] T) := by
      rw [tendsto_nhdsWithin_iff, ← hsq]
      refine ⟨?_, ?_⟩
      · have hc : Continuous fun t : ℝ => lam ^ 2 * t := continuous_const.mul continuous_id
        simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_lt_of_lt_one_right hlam2 ht
    exact hbkm.comp hmap

end Work.SolutionDelivery
