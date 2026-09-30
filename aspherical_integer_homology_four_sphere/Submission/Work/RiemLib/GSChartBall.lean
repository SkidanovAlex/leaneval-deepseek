import Submission.Work.RiemLib.GSHalfDisk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The exponential chart on a ball of *arbitrary* small radius

`GSDisk.exists_pos_homeo_closedBall` produces one (unnamed) radius `εG` at which the exponential
chart `u ↦ GExp x₀ u` is a homeomorphism onto the metric ball `{d(x₀,·) ≤ εG}`.  For the cap
argument of the Grove–Shiohama sphere theorem we need the same chart at *every* radius below
`εG`, together with the distance identity `d(x₀, GExp x₀ u) = ‖u‖` on that ball (which is what
makes the ray from `x₀` in direction `u` a *minimising* geodesic).

Both are consequences of the single chart at radius `εG` plus Hopf–Rinow and the injectivity of
the chart:

* for the identity, a shortest vector `v` with `GExp x₀ v = GExp x₀ u` and `‖v‖ = d(x₀, GExp x₀ u)`
  lies in the ball of radius `εG`, and injectivity forces `v = u`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.Distance
open Submission.EDist
open Submission.GlobalExp

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSChartBall

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable [PathConnectedSpace M] [RegularSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The exponential chart at every radius below the disk radius.**  There is `ε₀ > 0` such that
for every `t ∈ (0,ε₀)` the map `u ↦ GExp x₀ u` is a homeomorphism from the closed ball of radius
`t` in the tangent space onto `{d(x₀,·) ≤ t}`, and `d(x₀, GExp x₀ u) = ‖u‖` for `‖u‖ ≤ t`. -/
theorem exists_pos_homeo_closedBall_of_radius
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t ∈ Set.Ioo (0 : ℝ) ε₀,
      (∀ u : TangentSpace I x₀, ‖u‖ ≤ t →
        Manifold.riemannianEDist I x₀ (GExp (cov := cov) hmet x₀ u) = ENNReal.ofReal ‖u‖) ∧
      ∃ e : Metric.closedBall (0 : TangentSpace I x₀) t ≃ₜ
          {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t},
        ∀ u : Metric.closedBall (0 : TangentSpace I x₀) t,
          (e u : M) = GExp (cov := cov) hmet x₀ (u : TangentSpace I x₀) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨εG, hεG, eG, heG⟩ :=
    Submission.GSDisk.exists_pos_homeo_closedBall (cov := cov) hmet htor x₀
  obtain ⟨ρ, hρ, hρdist⟩ :=
    Submission.GlobalExp.exists_pos_riemannianEDist_GExp_eq (cov := cov) hmet htor x₀
  refine ⟨min εG ρ, lt_min hεG hρ, ?_⟩
  intro t ht
  have htpos : 0 < t := ht.1
  have hteG : t < εG := lt_of_lt_of_le ht.2 (min_le_left εG ρ)
  have htρ : t < ρ := lt_of_lt_of_le ht.2 (min_le_right εG ρ)
  have hle : t ≤ εG := le_of_lt hteG
  have hdist : ∀ u : TangentSpace I x₀, ‖u‖ ≤ t →
      Manifold.riemannianEDist I x₀ (GExp (cov := cov) hmet x₀ u) = ENNReal.ofReal ‖u‖ := by
    intro u hu
    have hlt : ‖u‖ < ρ := lt_of_le_of_lt hu htρ
    have h := hρdist u hlt
    rw [Submission.GSDisk.chartGram_self_fibre, Real.sqrt_sq (norm_nonneg u)] at h
    exact h
  refine ⟨hdist, ?_⟩
  have hiff : ∀ u : Metric.closedBall (0 : TangentSpace I x₀) εG,
      (u : TangentSpace I x₀) ∈ Metric.closedBall (0 : TangentSpace I x₀) t ↔
        (eG u : M) ∈ {y : M | Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t} := by
    intro u
    rw [Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro hu
      rw [Set.mem_ofPred_eq]
      have h2 := hdist (u : TangentSpace I x₀) hu
      rw [heG u, h2]
      exact ENNReal.ofReal_le_ofReal hu
    · intro hy
      have hy' : Manifold.riemannianEDist I x₀ (eG u : M) ≤ ENNReal.ofReal t := hy
      obtain ⟨v, hvG, hvd⟩ :=
        Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor x₀ (eG u : M)
      have hvel : ‖v‖ ≤ t := by
        rw [hvd, ENNReal.ofReal_le_ofReal_iff htpos.le] at hy'
        exact hy'
      have hvball : ‖v‖ ≤ εG := le_trans hvel hle
      have hvmem0 : v ∈ Metric.closedBall (0 : TangentSpace I x₀) εG := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hvball
      have heqM : (eG ⟨v, hvmem0⟩ : M) = (eG u : M) := by
        rw [heG ⟨v, hvmem0⟩, hvG]
      have hvmem : (⟨v, hvmem0⟩ : Metric.closedBall (0 : TangentSpace I x₀) εG) = u :=
        eG.injective (Subtype.ext heqM)
      rw [← Subtype.ext_iff.mp hvmem]
      exact hvel
  haveI : FiniteDimensional ℝ (TangentSpace I x₀) := ‹FiniteDimensional ℝ E›
  let nestD := Submission.GSHalfDisk.subtypeNestHomeomorph
      (s := Metric.closedBall (0 : TangentSpace I x₀) εG)
      (t := Metric.closedBall (0 : TangentSpace I x₀) t) (fun a ha => le_trans ha hle)
  let nestC := Submission.GSHalfDisk.subtypeNestHomeomorph
      (s := {y : M | Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal εG})
      (t := {y : M | Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t})
      (fun a ha => le_trans ha (ENNReal.ofReal_le_ofReal hle))
  let e1 : Metric.closedBall (0 : TangentSpace I x₀) t ≃ₜ
      {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal t} :=
    nestD.symm.trans ((eG.subtype
      (p := fun u : Metric.closedBall (0 : TangentSpace I x₀) εG =>
        (u : TangentSpace I x₀) ∈ Metric.closedBall (0 : TangentSpace I x₀) t)
      (q := fun y : {y : M // Manifold.riemannianEDist I x₀ y ≤ ENNReal.ofReal εG} =>
        (y : M) ∈ {z : M | Manifold.riemannianEDist I x₀ z ≤ ENNReal.ofReal t}) hiff).trans nestC)
  have hval : ∀ u : Metric.closedBall (0 : TangentSpace I x₀) t,
      (e1 u : M) = GExp (cov := cov) hmet x₀ (u : TangentSpace I x₀) := by
    intro u
    have hmem : (u : TangentSpace I x₀) ∈ Metric.closedBall (0 : TangentSpace I x₀) εG :=
      le_trans (by simpa only [Metric.mem_closedBall, dist_zero_right] using u.2) hle
    show (eG ⟨(u : TangentSpace I x₀), hmem⟩ : M) = _
    rw [heG]
  exact ⟨e1, hval⟩

end

end Submission.GSChartBall
