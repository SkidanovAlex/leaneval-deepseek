/-
The integrability conjuncts of a pointwise-dominated integrand.

`integrableConjuncts` turns a pointwise domination on the open quadrant (`|F| ≤ H`, with `F`
continuous there and vanishing at `z = 0`, and `H` with integrable angular slices and
integrable `z`-marginal) into the integrability of the angular slices of `F` and of its
`z`-marginal.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

set_option maxHeartbeats 1600000

/-- If `F` is continuous on the open quadrant, vanishes at `z = 0`, and is dominated on the
open quadrant by `H` whose angular slices and `z`-marginal are integrable, then the angular
slices and the marginal of `F` are integrable. -/
theorem integrableConjuncts {F H : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)))
    (hH : MeasureTheory.AEStronglyMeasurable (Function.uncurry H)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hzero : ∀ θ : ℝ, F 0 θ = 0)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => H z θ) Work.Spaces.Iθ)
    (hmarg : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, H z θ) Work.Spaces.Iz)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |F z θ| ≤ H z θ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) Work.Spaces.Iz := by
  have hFU : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      rw [show (fun θ : ℝ => F 0 θ) = fun _ => (0 : ℝ) from funext hzero]
      exact integrableOn_zero
    · refine MeasureTheory.Integrable.mono' (hsl z hz)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hF hzpos) ?_
      rw [restrict_Iθ_eq_Ioo]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs]
      exact hpt z θ hzpos hθ.1 hθ.2
  refine ⟨hFU, ?_⟩
  refine MeasureTheory.Integrable.mono' hmarg
    (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd _ hF)) ?_
  rw [restrict_Iz_eq_Ioi]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  rw [Real.norm_eq_abs]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have habs : MeasureTheory.IntegrableOn (fun θ => |F z θ|) Work.Spaces.Iθ := (hFU z hzI).norm
  refine MeasureTheory.integral_mono_ae habs (hsl z hzI) ?_
  rw [restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => hpt z θ hz hθ.1 hθ.2)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
