import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.Defs
import Submission.Work.ConstructionInstance.hasDerivAt_selfSimVort_slice
import Submission.Work.ConstructionInstance.bddDt_selfSimVort
import Submission.Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice
import Submission.Work.CoreResiduals.solVort_timeDeriv_aesm_preWindow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- The constructed vorticity satisfies the time-regularity bundle of the space-time Schauder
estimate on every strip: `Work.CoreResiduals.TimeDerivStrip (solVort P) S` for `0 < S < P.T`.

The three conjuncts are: `t`-differentiability of each slice on `Icc 0 S`
(`Work.ConstructionInstance.hasDerivAt_selfSimVort_slice`, applicable since
`Icc 0 S ⊆ preWindow P.T`), a uniform bound on `∂ₜω` there (`solVort_bddDt` together with the
lower bound `λ̄ ≥ (T-S)/2` from `hlam_low`), and the ae-strong-measurability of the derivative
slices (`Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice`, from the differentiability
in `t` and the measurability of the slices; the companion module
`Work.CoreResiduals.solVort_timeDeriv_aesm_preWindow` supplies it on `preWindow P.T`). -/
theorem solVort_timeDerivStrip {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {S : ℝ} (hS : 0 < S) (hST : S < P.T) :
    Work.CoreResiduals.TimeDerivStrip (Work.ConstructionInstance.solVort P) S := by
  have hδpos : 0 < (P.T - S) / 2 := by linarith
  have hδ2pos : 0 < ((P.T - S) / 2) ^ 2 := by positivity
  -- the strip `Icc 0 S` is contained in the half-window where the modulation data lives
  have hsub : ∀ t ∈ Set.Icc (0 : ℝ) S, t ∈ Work.ConstructionInstance.preWindow P.T :=
    fun t ht => ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hST⟩
  refine ⟨?_, ⟨P.M₁ / ((P.T - S) / 2) ^ 2, ?_⟩, ?_⟩
  · -- `t`-differentiability of each slice on the strip
    intro t ht y
    have hd := Work.ConstructionInstance.hasDerivAt_selfSimVort_slice
      (p := Work.ConstructionInstance.profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) P.hgdiff P.hlam P.hlamdif (hsub t ht) y
    simpa only [Work.ConstructionInstance.solVort] using hd
  · -- uniform bound on `∂ₜω` on the strip: `λ̄ ≥ (T-S)/2` there
    intro t ht y
    have htpre := hsub t ht
    have hδle : (P.T - S) / 2 ≤ P.lam t := by
      have h1 := P.hlam_low t ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
      linarith [ht.2]
    have hlt : 0 < P.lam t := P.hlam t htpre
    have hm2 : ((P.T - S) / 2) ^ 2 ≤ (P.lam t) ^ 2 := by
      have h := mul_le_mul hδle hδle hδpos.le hlt.le
      simpa only [pow_two] using h
    have h1 : ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t‖
        ≤ P.M₁ / (P.lam t) ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (P.lam t) ^ 2), mul_comm]
      exact Work.ConstructionInstance.solVort_bddDt P t htpre y
    have h2 : P.M₁ / (P.lam t) ^ 2 ≤ P.M₁ / ((P.T - S) / 2) ^ 2 :=
      div_le_div_of_nonneg_left P.hM₁ hδ2pos hm2
    linarith
  · -- ae-strong-measurability of the derivative slices
    intro t ht
    exact solVort_timeDeriv_aesm_preWindow P t (hsub t ht)

end Work.CoreResiduals
