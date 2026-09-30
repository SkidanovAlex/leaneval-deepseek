import Mathlib
import Submission.Work.RiemLib.RauchK
import Submission.Work.RiemLib.Geodesic
import Submission.Work.RiemLib.GeodesicSpeed
import Submission.Work.RiemLib.Length
import Submission.Work.RiemLib.Distance
import Submission.Work.RiemLib.InjRadius
import Submission.Work.RiemLib.InjBall
import Submission.Work.RiemLib.SegmentDomain
import Submission.Work.RiemLib.XuMain
import Submission.Work.RiemLib.EDist
import Submission.Work.RiemLib.GExpRay2
import Submission.Work.RiemLib.GExpJoint
import Submission.Work.RiemLib.GExpFlow
import Submission.Work.RiemLib.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt
import Submission.Work.RiemLib.GeodesicGlobal
import Submission.Work.RiemLib.GExpLocalInj
import Submission.Work.RiemLib.CutStep2
import Submission.Work.RiemLib.XuLift
import Submission.Work.RiemLib.ChartPieces
import Submission.Work.RiemLib.ChartIndep
import Submission.Work.RiemLib.CoeffSmooth2
import Submission.Work.RiemLib.JacobiGlobal
import Submission.Work.RiemLib.Commons.Analysis.ODE.exists_linearODE_solution_Icc
import Submission.Work.RiemLib.IndexCorner2
import Submission.Work.RiemLib.InjHalf
import Submission.Work.RiemLib.LensLoop
import Submission.Work.RiemLib.UniformInj
import Submission.Work.RiemLib.ConjRadius
import Submission.Work.RiemLib.ConjCut
import Submission.Work.RiemLib.SingularConj
import Submission.Work.RiemLib.RayConj
import Submission.Work.RiemLib.Gauss
import Submission.Work.RiemLib.ExpBound2
import Submission.Work.RiemLib.JacobiGauss
import Submission.Work.RiemLib.Minimal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- **Tangential chain rule along a variation of the global exponential map.**  The velocity at `0`
of the variation `r ↦ GExp p (t • (v + r • η))` is the differential of `w ↦ GExp p w` at `t • v`
applied to `t • η`. -/
lemma curveVelocity_GExp_smul_variation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {p : M} (t : ℝ) (v η : TangentSpace I p) :
    Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (v + r • η))) 0
      = (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w)
          (t • v)) (t • η) := by
  have h1 : HasDerivAt (fun r : ℝ => v + r • η) η (0 : ℝ) :=
    (((hasDerivAt_id (0 : ℝ)).smul_const η).const_add v).congr_deriv (one_smul ℝ η)
  have hσ : HasDerivAt (fun r : ℝ => t • (v + r • η)) (t • η) (0 : ℝ) := h1.const_smul t
  have hcont := Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p
    (t • (v + (0 : ℝ) • η))
  have hsm : MDifferentiableAt 𝓘(ℝ, E) I
      (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • (v + (0 : ℝ) • η)) :=
    hcont.mdifferentiableAt (by norm_num)
  have h := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp (I := I)
    (f := fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w)
    (σ := fun r : ℝ => t • (v + r • η)) (σ' := fun _ : ℝ => t • η)
    (γ := fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (v + r • η)))
    (t := 0) hσ hsm (Filter.EventuallyEq.refl _ _)
  have hpt : t • (v + (0 : ℝ) • η) = t • v := by rw [zero_smul, add_zero]
  rw [hpt] at h
  exact h

/-- **Tangential chain rule along a ray of the global exponential map.**  The velocity at `t` of the
ray `s ↦ GExp p (s • v)` is the differential of `w ↦ GExp p w` at `t • v` applied to `v`. -/
lemma curveVelocity_GExp_ray_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {p : M} (t : ℝ) (v : TangentSpace I p) :
    Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t
      = (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w)
          (t • v)) v := by
  have hσ : HasDerivAt (fun s : ℝ => s • v) v t :=
    ((hasDerivAt_id t).smul_const v).congr_deriv (one_smul ℝ v)
  have hsm : MDifferentiableAt 𝓘(ℝ, E) I
      (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v) :=
    (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p (t • v)).mdifferentiableAt
      (by norm_num)
  have h := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp (I := I)
    (f := fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w)
    (σ := fun s : ℝ => s • v) (σ' := fun _ : ℝ => v)
    (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v))
    (t := t) hσ hsm (Filter.EventuallyEq.refl _ _)
  exact h

theorem gauss_pairing_rescale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {v η u : TangentSpace I p}
    (hv : v ≠ 0) (hu1 : ‖u‖ = 1) (hcu : v = ‖v‖ • u)
    (H : ∀ t : ℝ,
      Inner.inner ℝ
        (Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0)
        (Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) t)
      = t * Inner.inner ℝ η u) :
    ∀ t : ℝ,
      Inner.inner ℝ
        (Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (v + r • η))) 0)
        (Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t)
      = t * Inner.inner ℝ η v := by
  intro t
  have hlampos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlamne : ‖v‖ ≠ 0 := ne_of_gt hlampos
  -- the two points `(t * ‖v‖) • u` and `t • v` coincide
  have hpt : (t * ‖v‖) • u = t • v := by rw [← smul_smul, ← hcu]
  -- the differential of `w ↦ GExp p w`, in the two descriptions of the common point
  have hM : (mfderiv 𝓘(ℝ, E) I
        (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) ((t * ‖v‖) • u))
      = (mfderiv 𝓘(ℝ, E) I
        (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) :=
    mfderiv_congr_point (I := 𝓘(ℝ, E)) (I' := I) hpt
  -- the `η`-coefficient comparison
  have hsmulη : (t * ‖v‖) • η = ‖v‖ • (t • η) := by rw [mul_comm t ‖v‖, ← smul_smul]
  -- the inner-product identity for the right-hand side
  have hinner : Inner.inner ℝ η v = ‖v‖ * Inner.inner ℝ η u :=
    (congrArg (fun z => Inner.inner ℝ η z) hcu).trans (real_inner_smul_right η u ‖v‖)
  -- first-curve relation
  have hrel1 :
      Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (v + r • η))) 0
      = ‖v‖⁻¹ • Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + r • η))) 0 := by
    have hA := curveVelocity_GExp_smul_variation (cov := cov) hmet t v η
    have hB := curveVelocity_GExp_smul_variation (cov := cov) hmet (t * ‖v‖) u η
    have e1 : Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + r • η))) 0
        = (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w)
            (t • v)) ((t * ‖v‖) • η) :=
      hB.trans (congrArg (fun L : E →L[ℝ] E => L ((t * ‖v‖) • η)) hM)
    have e2 : (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w)
            (t • v)) ((t * ‖v‖) • η)
        = ‖v‖ • (mfderiv 𝓘(ℝ, E) I
            (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) (t • η) :=
      (congrArg (fun z : E => (mfderiv 𝓘(ℝ, E) I
          (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) z) hsmulη).trans
        (map_smul (mfderiv 𝓘(ℝ, E) I
          (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) ‖v‖ (t • η))
    have e3 : ‖v‖⁻¹ • (‖v‖ • (mfderiv 𝓘(ℝ, E) I
            (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) (t • η))
        = (mfderiv 𝓘(ℝ, E) I
            (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) (t • η) := by
      rw [← mul_smul, inv_mul_cancel₀ hlamne, one_smul]
    calc Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (v + r • η))) 0
        = (mfderiv 𝓘(ℝ, E) I
            (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) (t • η) := hA
      _ = ‖v‖⁻¹ • (‖v‖ • (mfderiv 𝓘(ℝ, E) I
            (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) (t • η)) :=
            e3.symm
      _ = ‖v‖⁻¹ • ((mfderiv 𝓘(ℝ, E) I
            (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v))
              ((t * ‖v‖) • η)) :=
            congrArg (fun z : E => ‖v‖⁻¹ • z) e2.symm
      _ = ‖v‖⁻¹ • Submission.Geodesic.curveVelocity (I := I)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + r • η))) 0 :=
            congrArg (fun z : E => ‖v‖⁻¹ • z) e1.symm
  -- second-curve relation
  have hrel2 :
      Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t
      = ‖v‖ • Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) (t * ‖v‖) := by
    have hA := curveVelocity_GExp_ray_tangent (cov := cov) hmet t v
    have hB := curveVelocity_GExp_ray_tangent (cov := cov) hmet (t * ‖v‖) u
    have e1 : Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) (t * ‖v‖)
        = (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w)
            (t • v)) u :=
      hB.trans (congrArg (fun L : E →L[ℝ] E => L u) hM)
    have e2 : (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w)
            (t • v)) v
        = ‖v‖ • (mfderiv 𝓘(ℝ, E) I
            (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) u :=
      (congrArg (fun z : E => (mfderiv 𝓘(ℝ, E) I
          (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) z) hcu).trans
        (map_smul (mfderiv 𝓘(ℝ, E) I
          (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) ‖v‖ u)
    calc Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t
        = (mfderiv 𝓘(ℝ, E) I
            (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) v := hA
      _ = ‖v‖ • (mfderiv 𝓘(ℝ, E) I
            (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p w) (t • v)) u := e2
      _ = ‖v‖ • Submission.Geodesic.curveVelocity (I := I)
            (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) (t * ‖v‖) :=
            congrArg (fun z : E => ‖v‖ • z) e1.symm
  -- canonical point of the goal's first velocity: `GExp p (t • (v + 0 • η))`
  let A := TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (t • (v + (0 : ℝ) • η)))
  -- rewrite the point of `GExp` in `H`'s statement to this canonical point
  have hcanon3 : (t * ‖v‖) • (u + (0 : ℝ) • η) = t • (v + (0 : ℝ) • η) := by
    simp only [zero_smul, add_zero]
    rw [← smul_smul, ← hcu]
  have hcanonG3 : Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + (0 : ℝ) • η))
      = Submission.GlobalExp.GExp (cov := cov) hmet p (t • (v + (0 : ℝ) • η)) :=
    congrArg (fun z => Submission.GlobalExp.GExp (cov := cov) hmet p z) hcanon3
  have hH := H (t * ‖v‖)
  rw [hcanonG3] at hH
  -- the chain of equalities in `ℝ`, all inner products at the instance determined by `A`
  have step1 : Inner.inner ℝ
        (show A from Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (v + r • η))) 0)
        (show A from Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t)
      = Inner.inner ℝ
        (show A from ‖v‖⁻¹ • Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + r • η))) 0)
        (show A from Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t) :=
    congrArg (fun z : A => Inner.inner ℝ z (show A from Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t)) hrel1
  have step2 : Inner.inner ℝ
        (show A from ‖v‖⁻¹ • Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + r • η))) 0)
        (show A from Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • v)) t)
      = Inner.inner ℝ
        (show A from ‖v‖⁻¹ • Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + r • η))) 0)
        (show A from ‖v‖ • Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) (t * ‖v‖)) :=
    congrArg (fun z => Inner.inner ℝ (show A from ‖v‖⁻¹ • Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + r • η))) 0) z) hrel2
  have step3 : Inner.inner ℝ
        (show A from ‖v‖⁻¹ • Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + r • η))) 0)
        (show A from ‖v‖ • Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) (t * ‖v‖))
      = Inner.inner ℝ
        (show A from Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + r • η))) 0)
        (show A from Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) (t * ‖v‖)) := by
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hlamne, one_mul]
  have step4 : Inner.inner ℝ
        (show A from Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((t * ‖v‖) • (u + r • η))) 0)
        (show A from Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) (t * ‖v‖))
      = (t * ‖v‖) * Inner.inner ℝ η u := hH
  have step5 : (t * ‖v‖) * Inner.inner ℝ η u = t * Inner.inner ℝ η v := by
    rw [hinner]
    ring
  exact step1.trans (step2.trans (step3.trans (step4.trans step5)))

end Work.OddBound.longHomotopy
