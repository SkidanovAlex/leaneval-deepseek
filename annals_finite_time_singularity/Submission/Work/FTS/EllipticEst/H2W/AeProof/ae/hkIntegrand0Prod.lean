import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint integrability of the level-`0` integrand over `Iz × Iθ`

The level-`0` integrand `HkIntegrand α 0 f` is the single square
`(f · w / sin(2θ)^{η/2})²` (there are no derivative slots when `k = 0`), so it is continuous
on the open quadrant whenever `f` is, hence a.e. strongly measurable for the product of the
restrictions of Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`.  The hypothesis
`HkMem α 0 f` supplies integrability of every angular slice and of the outer integral, and
`Work.Spaces.integrable_prod_of_iterated` (Tonelli, in the nonnegative case) then yields joint
integrability over `Iz × Iθ`.
-/

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- For `θ ∈ (0, π/2)` the sine `sin(2θ)` is positive. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The level-`0` integrand is the single square `(f · w / sin(2θ)^{η/2})²`, because the
sums defining `HkIntegrand` are indexed by `range (0+1) = {0}` and the mixed slot
requires `1 ≤ i` with `i + j ≤ 0`, hence never occurs. -/
theorem hkIntegrand_zero_eq' (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- The level-`0` integrand is continuous on the open quadrant whenever `f` is. -/
theorem continuousOn_hkIntegrand_zero (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hp.2)))
  have hprod : ContinuousOn
      (fun p : ℝ × ℝ =>
        f p.1 p.2 * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hf.mul (hw.div hsin
      (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hp.2) _)))
  refine (hprod.pow 2).congr ?_
  intro p _
  exact hkIntegrand_zero_eq' α f p.1 p.2

theorem hkIntegrand0Prod {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ ⊤ (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 0 f
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α 0 f z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_hkIntegrand_zero α f hsm.continuousOn)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 0 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      (fun z hz => hmem.1 z hz)
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α 0 f z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  exact (Work.Spaces.integrable_prod_of_iterated hnn haesm hslice houter).1

end

end Work.FTS.EllipticEst.H2W.AeProof.ae
