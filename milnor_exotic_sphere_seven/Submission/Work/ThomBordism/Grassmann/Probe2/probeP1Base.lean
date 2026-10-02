import Mathlib
import Submission.Work.ThomBordism.Grassmann.Probe2.probeBaseDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism.Grassmann.Probe2

open Work.TangentClasses
open Work.Projective

noncomputable section

/-- **The probe at the base case `(k, m) = (2, 4)`.**

The map `σ : ℂP² → G̃r₂(ℝ⁶)`, `[v] ↦ ℝ·v + ℝ·iv`, pulls the first Pontryagin class of the
tautological oriented rank-`2` bundle back to `∓ p₁(zStd)`, where `zStd` is the realification of
the tautological dual line bundle of `ℂP²`. -/
theorem probeP1Base :
    ∃ σ : C(Work.Projective.CP 2, Work.ThomBordism.Grassmann.OG 2 4),
      (Work.Thom.CohMap σ ℤ 4).hom (Work.ThomBordism.Grassmann.p1 2 4)
        = Work.Thom.pontryagin1 Work.ThomBordism.Grassmann.zStd ∨
      (Work.Thom.CohMap σ ℤ 4).hom (Work.ThomBordism.Grassmann.p1 2 4)
        = - Work.Thom.pontryagin1 Work.ThomBordism.Grassmann.zStd := by
  obtain ⟨e⟩ := probeSigma_iso
  refine ⟨sigma2, Or.inl ?_⟩
  rw [show p1 2 4 = Work.Thom.pontryagin1 (tautologicalBundle 2 4) from by
    rw [p1, Work.Thom.pontryaginClass_one]]
  rw [← Work.Thom.pontryagin1_comap (tautologicalBundle 2 4) sigma2]
  exact pontryagin1_eq_of_bundleIso _ _ e

end

end Work.ThomBordism.Grassmann.Probe2
