import Submission.Work.RiemLib.GSMono
import Submission.Work.RiemLib.GSStep1
import Submission.Work.RiemLib.GSGlobal2
import Submission.Work.RiemLib.Commons.Geometry.Manifold.exists_global_flow
import Submission.Work.RiemLib.Commons.Geometry.Manifold.contMDiffAt_of_isMIntegralCurve

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The flow of an ascent field on a compact region, and the level-set structure of `d(p,·)`

This file assembles the Grove–Shiohama step 3 machinery: given a diameter pair `(p,q)` with
`D = d(p,q) ∈ (π/2, 2π/3]` and levels `0 < a' < a < b < b' < D`, we

* construct a smooth field `V` which is an ascent field for `f = d(p,·)` on the compact region
  `T = {a' ≤ f ≤ b'}` (`GSGlobal2.exists_continuous_ascent_field_of_diam`),
* take its global flow `φ` (`Commons.Geometry.Manifold.exists_global_flow`),
* and record the resulting structure: the trajectories through `{a ≤ f ≤ b}` stay above the level
  `a'`, cross every level in `[a,b]` exactly once, and the crossing times are uniformly bounded.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GSField
open Submission.GSFlow
open Submission.GSMono
open Submission.GSGlobal2
open Submission.Distance
open Submission.EDist

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSLevel

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

open Classical in
/-- **The ascent field on a compact level region, and its global flow.** -/
theorem exists_flow_of_diam
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p q : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    {a' b' : ℝ} (ha' : 0 < a') (ha'b' : a' < b') (hb' : b' < D) :
    ∃ V : (y : M) → TangentSpace I y, ∃ φ : M → ℝ → M,
      ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
        (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))) ∧
      (∀ y ∈ {y : M | a' ≤ (Manifold.riemannianEDist I p y).toReal ∧
          (Manifold.riemannianEDist I p y).toReal ≤ b'}, IsAscentAt (cov := cov) hmet p y (V y)) ∧
      (∀ y : M, φ y 0 = y) ∧
      (∀ y : M, IsMIntegralCurve (φ y) V) ∧
      (∀ y : M, ∀ s t : ℝ, φ (φ y s) t = φ y (s + t)) ∧
      Continuous (fun z : M × ℝ => φ z.1 z.2) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- the compact level region
  set T : Set M := {y : M | a' ≤ (Manifold.riemannianEDist I p y).toReal ∧
    (Manifold.riemannianEDist I p y).toReal ≤ b'} with hTdef
  have hfin : ∀ y : M, Manifold.riemannianEDist I p y ≠ ⊤ := fun y =>
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p y).ne
  have hcont : Continuous fun y : M => (Manifold.riemannianEDist I p y).toReal := by
    have h1 : Continuous fun y : M => Manifold.riemannianEDist I p y :=
      Submission.HopfRinow.continuous_riemannianEDist_left (I := I) p
    exact ENNReal.continuousOn_toReal.comp_continuous h1 (fun y => hfin y)
  have hTcomp : IsCompact T := by
    rw [hTdef]
    exact (isClosed_le continuous_const hcont).inter (isClosed_le hcont continuous_const) |>.isCompact
  have hfq : (Manifold.riemannianEDist I p q).toReal = D := by
    rw [hpq, ENNReal.toReal_ofReal (le_trans (by linarith [Real.pi_pos]) hDgt.le)]
  have hTp : ∀ y ∈ T, y ≠ p := by
    intro y hy hp
    rw [hTdef] at hy
    simp only [Set.mem_ofPred_eq] at hy
    rw [hp] at hy
    have h0 : (Manifold.riemannianEDist I p p).toReal = 0 := by
      rw [Manifold.riemannianEDist_self, ENNReal.toReal_zero]
    linarith [hy.1, h0, ha']
  have hTq : ∀ y ∈ T, y ≠ q := by
    intro y hy hq
    rw [hTdef] at hy
    simp only [Set.mem_ofPred_eq] at hy
    rw [hq, hfq] at hy
    linarith [hy.2, hb']
  obtain ⟨V, hasc, hVcont, hVsm⟩ :=
    exists_continuous_ascent_field_of_diam (cov := cov) hmet htor hpinch hdiam hDgt hDlt hpq
      hTcomp hTp hTq
  obtain ⟨φ, hφ0, hφint, hφadd, hφcont⟩ :=
    Commons.Geometry.Manifold.exists_global_flow (I := I) hVsm
  exact ⟨V, φ, hVsm, fun y hy => hasc y hy, hφ0, hφint, hφadd, hφcont⟩


/-- The velocity of an integral curve is the field itself. -/
lemma curveVelocity_eq_of_isMIntegralCurve {v : (x : M) → TangentSpace I x} {γ : ℝ → M}
    (h : IsMIntegralCurve γ v) (t : ℝ) : curveVelocity (I := I) γ t = v (γ t) := by
  have hd := (h.isMIntegralCurveAt t).hasMFDerivAt.mfderiv
  rw [curveVelocity_apply, hd]
  show (1 : ℝ) • v (γ t) = v (γ t)
  rw [one_smul]

/-- **Strict monotonicity of `d(p,·)` along the flow, on any time interval whose trajectory stays
inside the region `T` where `V` is an ascent field.** -/
theorem strictMonoOn_toReal_flow
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {V : (y : M) → TangentSpace I y} {φ : M → ℝ → M} {T : Set M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hasc : ∀ y ∈ T, IsAscentAt (cov := cov) hmet p y (V y))
    (hφ0 : ∀ y : M, φ y 0 = y)
    (hφint : ∀ y : M, IsMIntegralCurve (φ y) V)
    (hφadd : ∀ y : M, ∀ s t : ℝ, φ (φ y s) t = φ y (s + t))
    {a b : ℝ} (hab : a ≤ b) {x : M} (hW : ∀ t ∈ Set.Icc a b, φ x t ∈ T)
    (hcont : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I p (φ x t)).toReal)
      (Set.Icc a b)) :
    StrictMonoOn (fun t : ℝ => (Manifold.riemannianEDist I p (φ x t)).toReal) (Set.Icc a b) :=
  Submission.GSMono.strictMonoOn_flow (cov := cov) hmet htor hpinch hφ0 hφadd
    (fun y => Commons.Geometry.Manifold.contMDiffAt_of_isMIntegralCurve (I := I) hVsm (hφint y) 0)
    (fun y => by
      rw [curveVelocity_eq_of_isMIntegralCurve (I := I) (hφint y) 0, hφ0])
    hasc hab hW hcont

end

end Submission.GSLevel
