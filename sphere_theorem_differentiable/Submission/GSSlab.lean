import Submission.GSLevel
import Submission.GSStep1
import Submission.GSCross
import Submission.Commons.Topology.homeo_level_times_of_flow_crossing
import Submission.Commons.Topology.homeo_level_times_of_flow_crossing_formula

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The level-set structure of `d(p,·)` on a slab (Grove--Shiohama step 3(b))

This file instantiates the abstract crossing theorem `Submission.GSCross.exists_unique_crossing`
with the ascent field of `d(p,·)` produced by `Submission.GSLevel.exists_flow_of_diam`, and applies
the commons level-set homeomorphism `Commons.Topology.homeo_level_times_of_flow_crossing`.

The result `homeo_level_region_of_diam` is the missing input of Grove--Shiohama's step 3(b): the
slab `{a ≤ d(p,·) ≤ b}` (with `a' < a < b < b' < D = d(p,q)` and `D ≤ 2π/3`) is homeomorphic to
`{d(p,·) = a} × [0, b - a]`, i.e. the level sets of `d(p,·)` stack as spheres.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GSField
open Submission.GSFlow
open Submission.GSMono
open Submission.GSGlobal2
open Submission.GSLevel
open Submission.Distance
open Submission.EDist
open Submission.Length

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSSlab

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Grove--Shiohama step 3(b), level-set form.**  Let `(p,q)` be a diameter pair with
`π/2 < D = d(p,q) ≤ 2π/3` and let `a' < a < b < b' < D` with `0 < a'`.  Then the slab
`{a ≤ d(p,·) ≤ b}` is homeomorphic to the product of the level set `{d(p,·) = a}` with the interval
`[0, b-a]`. -/
theorem homeo_level_region_of_diam
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p q : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    {a' b' a b : ℝ} (ha' : 0 < a') (ha'b' : a' < b') (hb' : b' < D)
    (ha'a : a' < a) (hab : a < b) (hbb' : b < b') :
    Nonempty (({y : M | a ≤ (Manifold.riemannianEDist I p y).toReal ∧
        (Manifold.riemannianEDist I p y).toReal ≤ b}) ≃ₜ
      ({y : M | (Manifold.riemannianEDist I p y).toReal = a} ×ˢ
        Set.Icc (0 : ℝ) (b - a))) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨V, φ, hVsm, hasc, hφ0, hφint, hφadd, hφcont⟩ :=
    exists_flow_of_diam (cov := cov) hmet htor hpinch hdiam hDgt hDlt hpq ha' ha'b' hb'
  -- the function whose level sets we study
  set f : M → ℝ := fun y => (Manifold.riemannianEDist I p y).toReal with hfdef
  have hfin : ∀ y : M, Manifold.riemannianEDist I p y ≠ ⊤ := fun y =>
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p y).ne
  have hfcont : Continuous f := by
    have h1 : Continuous fun y : M => Manifold.riemannianEDist I p y :=
      Submission.HopfRinow.continuous_riemannianEDist_left (I := I) p
    exact ENNReal.continuousOn_toReal.comp_continuous h1 hfin
  -- the local ascent condition
  have hT : ∀ y : M, a' ≤ f y → f y ≤ b' →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Ioo (0 : ℝ) δ, f (φ y (-s)) < f y := by
    intro y hy1 hy2
    have hasc' : IsAscentAt (cov := cov) hmet p y (V y) := hasc y ⟨hy1, hy2⟩
    have hbase : (fun s : ℝ => φ y (-s)) 0 = y := by
      show φ y (-(0:ℝ)) = y
      rw [neg_zero]
      exact hφ0 y
    have hsm : ContMDiffAt 𝓘(ℝ) I ∞ (fun s : ℝ => φ y (-s)) 0 := by
      have hf' : ContMDiffAt 𝓘(ℝ) I ∞ (φ y) (-(0:ℝ)) := by
        rw [neg_zero]
        exact Commons.Geometry.Manifold.contMDiffAt_of_isMIntegralCurve (I := I) hVsm (hφint y) 0
      exact hf'.comp 0 contMDiffAt_id.neg
    have hvel : curveVelocity (I := I) (fun s : ℝ => φ y (-s)) 0 = -V y := by
      have hfun : (fun s : ℝ => φ y (-s)) = (fun s : ℝ => φ y ((-1:ℝ) * s + 0)) := by
        funext s; rw [neg_one_mul, add_zero]
      rw [hfun]
      have hmd : MDifferentiableAt 𝓘(ℝ) I (φ y) ((-1:ℝ) * 0 + 0) := by
        rw [mul_zero, add_zero]
        exact (Commons.Geometry.Manifold.contMDiffAt_of_isMIntegralCurve (I := I) hVsm
          (hφint y) 0).mdifferentiableAt (by simp)
      rw [curveVelocity_comp_mul_add (I := I) (γ := φ y) (c := -1) (d := 0) (t := 0) hmd,
        mul_zero, add_zero, neg_one_smul]
      have hv := curveVelocity_eq_of_isMIntegralCurve (I := I) (hφint y) 0
      rw [hφ0 y] at hv
      exact congrArg (fun w => -w) hv
    obtain ⟨δ, hδ, hδ'⟩ := flow_left_lt (cov := cov) hmet htor hpinch (p := p) (x := y)
      (V := V y) hasc' (σ := fun s : ℝ => φ y (-s)) hbase hsm hvel
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have hlt : Manifold.riemannianEDist I p (φ y (-s)) < Manifold.riemannianEDist I p y :=
      hδ' s hs
    exact (ENNReal.toReal_lt_toReal (hfin _) (hfin _)).mpr hlt
  -- the crossing structure
  obtain ⟨N, hN, hcross⟩ :=
    Submission.GSCross.exists_unique_crossing (X := M) hfcont hφ0 hφadd hφcont hT ha'b'
      ha'a hab hbb'
  exact Commons.Topology.homeo_level_times_of_flow_crossing hfcont hφ0 hφcont hφadd hab.le hN hcross

/-- **Grove--Shiohama step 3(b), level-set form (with the level parameter).**  Let `(p,q)` be a
diameter pair with `π/2 < D = d(p,q) ≤ 2π/3` and let `a' < a < b < b' < D` with `0 < a'`.  Then the
slab `{a ≤ d(p,·) ≤ b}` is homeomorphic to the product of the level set `{d(p,·) = a}` with the
interval `[0, b-a]`, the *fibre coordinate being the value of `d(p,·) - a`*. -/
theorem homeo_level_region_of_diam_formula
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p q : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    {a' b' a b : ℝ} (ha' : 0 < a') (ha'b' : a' < b') (hb' : b' < D)
    (ha'a : a' < a) (hab : a < b) (hbb' : b < b') :
    ∃ Φ : ({y : M | (Manifold.riemannianEDist I p y).toReal = a} ×ˢ
        Set.Icc (0 : ℝ) (b - a)) ≃ₜ
      {y : M | a ≤ (Manifold.riemannianEDist I p y).toReal ∧
        (Manifold.riemannianEDist I p y).toReal ≤ b},
      ∀ x, (Manifold.riemannianEDist I p ((Φ x : M))).toReal = a + (x.1.2 : ℝ) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨V, φ, hVsm, hasc, hφ0, hφint, hφadd, hφcont⟩ :=
    exists_flow_of_diam (cov := cov) hmet htor hpinch hdiam hDgt hDlt hpq ha' ha'b' hb'
  -- the function whose level sets we study
  set f : M → ℝ := fun y => (Manifold.riemannianEDist I p y).toReal with hfdef
  have hfin : ∀ y : M, Manifold.riemannianEDist I p y ≠ ⊤ := fun y =>
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p y).ne
  have hfcont : Continuous f := by
    have h1 : Continuous fun y : M => Manifold.riemannianEDist I p y :=
      Submission.HopfRinow.continuous_riemannianEDist_left (I := I) p
    exact ENNReal.continuousOn_toReal.comp_continuous h1 hfin
  -- the local ascent condition
  have hT : ∀ y : M, a' ≤ f y → f y ≤ b' →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Ioo (0 : ℝ) δ, f (φ y (-s)) < f y := by
    intro y hy1 hy2
    have hasc' : IsAscentAt (cov := cov) hmet p y (V y) := hasc y ⟨hy1, hy2⟩
    have hbase : (fun s : ℝ => φ y (-s)) 0 = y := by
      show φ y (-(0:ℝ)) = y
      rw [neg_zero]
      exact hφ0 y
    have hsm : ContMDiffAt 𝓘(ℝ) I ∞ (fun s : ℝ => φ y (-s)) 0 := by
      have hf' : ContMDiffAt 𝓘(ℝ) I ∞ (φ y) (-(0:ℝ)) := by
        rw [neg_zero]
        exact Commons.Geometry.Manifold.contMDiffAt_of_isMIntegralCurve (I := I) hVsm (hφint y) 0
      exact hf'.comp 0 contMDiffAt_id.neg
    have hvel : curveVelocity (I := I) (fun s : ℝ => φ y (-s)) 0 = -V y := by
      have hfun : (fun s : ℝ => φ y (-s)) = (fun s : ℝ => φ y ((-1:ℝ) * s + 0)) := by
        funext s; rw [neg_one_mul, add_zero]
      rw [hfun]
      have hmd : MDifferentiableAt 𝓘(ℝ) I (φ y) ((-1:ℝ) * 0 + 0) := by
        rw [mul_zero, add_zero]
        exact (Commons.Geometry.Manifold.contMDiffAt_of_isMIntegralCurve (I := I) hVsm
          (hφint y) 0).mdifferentiableAt (by simp)
      rw [curveVelocity_comp_mul_add (I := I) (γ := φ y) (c := -1) (d := 0) (t := 0) hmd,
        mul_zero, add_zero, neg_one_smul]
      have hv := curveVelocity_eq_of_isMIntegralCurve (I := I) (hφint y) 0
      rw [hφ0 y] at hv
      exact congrArg (fun w => -w) hv
    obtain ⟨δ, hδ, hδ'⟩ := flow_left_lt (cov := cov) hmet htor hpinch (p := p) (x := y)
      (V := V y) hasc' (σ := fun s : ℝ => φ y (-s)) hbase hsm hvel
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have hlt : Manifold.riemannianEDist I p (φ y (-s)) < Manifold.riemannianEDist I p y :=
      hδ' s hs
    exact (ENNReal.toReal_lt_toReal (hfin _) (hfin _)).mpr hlt
  -- the crossing structure
  obtain ⟨N, hN, hcross⟩ :=
    Submission.GSCross.exists_unique_crossing (X := M) hfcont hφ0 hφadd hφcont hT ha'b'
      ha'a hab hbb'
  exact Commons.Topology.homeo_level_times_of_flow_crossing_formula hfcont hφ0 hφcont hφadd hab.le hN hcross


end

end Submission.GSSlab
