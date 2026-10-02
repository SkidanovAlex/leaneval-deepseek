import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.Defs
import Submission.Work.ELRig.Sides
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear
import Submission.Work.Top.mem_paramRay_extAngle
import Submission.Work.Top.extAngle_of_mem_paramRay
import Submission.Work.ParamRays.isClosed_filledJulia

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

/-- The first root angle lies in `[0,1)`. -/
theorem alpha1_mem_Ico : Work.EL.alpha1 ∈ Set.Ico (0 : ℝ) 1 := by
  rw [Work.EL.alpha1]; norm_num

/-- The second root angle lies in `[0,1)`. -/
theorem alpha2_mem_Ico : Work.EL.alpha2 ∈ Set.Ico (0 : ℝ) 1 := by
  rw [Work.EL.alpha2]; norm_num

theorem exists_local_angle_at_lift {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P)
    {s : ℝ} (hre : (L.γ₁ s).re < -L.R) :
    ∃ D : Set ℂ, IsOpen D ∧ L.γ₁ s ∈ D ∧ D ⊆ {w : ℂ | w.re < -L.R} ∧
      (∀ w ∈ D, fl.Ψ w ∉ Work.EL.K c) ∧
      (∀ w ∈ D, (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w) = Work.EL.alpha1
          ↔ w ∈ Set.range L.γ₁)) ∧
      (∀ w ∈ D, Work.EL.InArc (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w))
          P.a P.b → fl.Ψ w ∈ Work.EL.pairSide P) ∧
      (∀ w ∈ D, Work.EL.InArc (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w))
          P.b (P.a + 1) → fl.Ψ w ∈ Work.EL.pairSideNear P) := by
  -- `Ψ` sends the base point to a ray point, hence off the filled Julia set.
  have hzK : fl.Ψ (L.γ₁ s) ∉ Work.EL.K c := by
    rw [L.hΨ₁ s]
    exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s)
  -- `K c` is closed, so some ball around `Ψ (γ₁ s)` misses it.
  obtain ⟨ε, hεpos, hεball⟩ :=
    Metric.isOpen_iff.mp (Work.ParamRays.isClosed_filledJulia c).isOpen_compl
      (fl.Ψ (L.γ₁ s)) hzK
  have hε : ∀ z : ℂ, dist z (fl.Ψ (L.γ₁ s)) < ε → z ∉ Work.EL.K c :=
    fun z hz => hεball (Metric.mem_ball.mpr hz)
  -- `Ψ` is continuous, and entire, so it is continuous at the base point.
  have hcont : Continuous fl.Ψ := fl.Ψ_diff.continuous
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp hcont.continuousAt ε hεpos
  refine ⟨Metric.ball (L.γ₁ s) δ ∩ {w : ℂ | w.re < -L.R},
    (Metric.isOpen_ball).inter (isOpen_lt Complex.continuous_re continuous_const),
    ⟨Metric.mem_ball_self hδpos, hre⟩, fun w hw => hw.2, ?_, ?_, ?_, ?_⟩
  · -- the image of the neighbourhood misses `K c`
    intro w hw
    exact hε (fl.Ψ w) (hδ (Metric.mem_ball.mp hw.1))
  · -- the external angle is `α₁` exactly on the lift
    intro w hw
    have hwK : fl.Ψ w ∉ Work.EL.K c := hε (fl.Ψ w) (hδ (Metric.mem_ball.mp hw.1))
    constructor
    · intro h
      have hmem : fl.Ψ w ∈ Work.Top.NakaneData.paramRay d.hN
          (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w)) :=
        Work.Top.mem_paramRay_extAngle d.hN hwK
      rw [h] at hmem
      exact L.tailId₁ w hw.2 hmem
    · rintro ⟨s', rfl⟩
      exact Work.Top.extAngle_of_mem_paramRay d.hN alpha1_mem_Ico.1 alpha1_mem_Ico.2
        (L.img₁ s')
  · -- the far arc maps into the far side
    intro w hw hIn
    have hwK : fl.Ψ w ∉ Work.EL.K c := hε (fl.Ψ w) (hδ (Metric.mem_ball.mp hw.1))
    have hmem : fl.Ψ w ∈ Work.Top.NakaneData.paramRay d.hN
        (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w)) :=
      Work.Top.mem_paramRay_extAngle d.hN hwK
    exact hside.paramRay_far _ hIn hmem
  · -- the near arc maps into the near side
    intro w hw hIn
    have hwK : fl.Ψ w ∉ Work.EL.K c := hε (fl.Ψ w) (hδ (Metric.mem_ball.mp hw.1))
    have hmem : fl.Ψ w ∈ Work.Top.NakaneData.paramRay d.hN
        (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w)) :=
      Work.Top.mem_paramRay_extAngle d.hN hwK
    exact hside.paramRay_near _ hIn hmem

end Work.ELRig
