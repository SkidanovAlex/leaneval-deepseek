import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.FireFix.Prime.physVort_support
import Submission.Work.FTS.FireFix.Prime.physVort_bound
import Submission.Work.FTS.FireFix.Prime.PhysVortHolderSlice
import Submission.Work.FTS.FireFix.Prime.physVort_holder_time
import Submission.Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound
import Submission.Work.FTS.FireFix.Prime.physVort_timeDeriv_aesm
import Submission.Work.FTS.FireFix.Prime.profFullHolder
import Submission.Work.FTS.FireFix.Prime.profFullBounds
import Submission.Work.FTS.FireFix.Prime.dzProfFullUniform
import Submission.Work.FTS.FireFix.Prime.dzProfFullZero
import Submission.Work.FTS.FireFix.Prime.dtgZero
import Submission.Work.FTS.FireFix.Prime.clockBounds
import Submission.Work.FTS.FireFix.Prime.clockLipschitz
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.FireFix.Prime.PvbHolder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology

open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-! ## The bundle -/

/-- **THE PHYSICAL VORTICITY OF A `RegPkg'` PROFILE IS STRIP-ADMISSIBLE (node N7).**  There is a
radius `R > 0` (bounding the support of `ω(·,τ)` uniformly on the strip) such that the physical
vorticity `ω = physVort α A B g` satisfies the full hypothesis bundle
`BSAdmissibleStripFull α ω R S` of the space–time Schauder estimate. -/
theorem physVort_bundle {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ∃ R : ℝ, 0 < R ∧
      Work.CoreResiduals.BSAdmissibleStripFull (⟨α, h.hα.le⟩ : NNReal)
        (Work.FTS.Regularity.physVort α A B g) R S := by
  obtain ⟨R, hR0, hsupp⟩ := physVort_support h
  obtain ⟨M, _hM0, hMb⟩ := physVort_bound h
  obtain ⟨H, hH⟩ := physVort_slice_holder h
  obtain ⟨N, _hN0, hNt⟩ := physVort_holder_time h
  obtain ⟨hderiv, M₁, _hM₁0, hM₁⟩ := physVort_hasDerivAt_and_bound h
  obtain ⟨Nd, _hNd0, hNd⟩ := pvb_timeDeriv_holder h
  refine ⟨R, hR0, ⟨?_, ?_, ?_⟩⟩
  · -- `BSAdmissibleStrip`
    refine ⟨hR0, hsupp, ⟨M, fun τ hτ y => hMb τ hτ y⟩, ⟨H, ?_⟩,
      ⟨N, fun y τ hτ τ' hτ' => hNt y τ hτ τ' hτ'⟩, ?_⟩
    · intro τ hτ
      exact hH τ hτ
    · intro τ hτ
      exact physVort_slice_aesm h τ hτ
  · -- `TimeDerivStrip`
    refine ⟨fun τ hτ y => hderiv y τ hτ, ⟨M₁, fun τ hτ y => hM₁ τ hτ y⟩, ?_⟩
    intro τ hτ
    exact physVort_timeDeriv_aesm h τ hτ
  · -- `TimeDerivStripHolder`
    exact ⟨Nd, fun y τ hτ τ' hτ' => hNd y τ hτ τ' hτ'⟩



end Work.FTS.FireFix.Prime