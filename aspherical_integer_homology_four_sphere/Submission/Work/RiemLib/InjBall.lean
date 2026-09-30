import Submission.Work.RiemLib.XuStep
import Submission.Work.RiemLib.GExpTranslate
import Submission.Work.RiemLib.CutWitness

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius
open Submission.HopfRinow

namespace Submission.InjBall

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The exponential map is onto the open ball.**  Every point `y` at Riemannian distance `< m`
from `p` is `GExp p v` for some `v` of norm `< m`. -/
theorem exists_tangent_of_edist_lt (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p y : M} {m : ℝ}
    (hy : Manifold.riemannianEDist I p y < ENNReal.ofReal m) :
    ∃ v : TangentSpace I p, ‖v‖ < m ∧ GExp (cov := cov) hmet p v = y := by
  obtain ⟨v, hvG, hvd⟩ := exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p y
  refine ⟨v, ?_, hvG⟩
  have hlt : ENNReal.ofReal ‖v‖ < ENNReal.ofReal m := by rw [← hvd]; exact hy
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg v)).mp hlt

/-- **Uniqueness of the tangent vector**: on the injectivity ball, `GExp p` is injective.  Combining
with `exists_tangent_of_edist_lt`: every point of the open ball of radius `m` around `p` is `GExp p v`
for a *unique* `v` of norm `< m`. -/
theorem exists_unique_tangent_of_edist_lt (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m) {y : M}
    (hy : Manifold.riemannianEDist I p y < ENNReal.ofReal m) :
    ∃! v : TangentSpace I p, ‖v‖ < m ∧ GExp (cov := cov) hmet p v = y := by
  obtain ⟨v, hvlt, hvG⟩ := exists_tangent_of_edist_lt (cov := cov) hmet htor hy
  refine ⟨v, ⟨hvlt, hvG⟩, ?_⟩
  rintro w ⟨hwlt, hwG⟩
  exact hinj w v hwlt hvlt (by rw [hwG, hvG])

/-- **On the injectivity ball the exponential map preserves the distance from the base point.**
For `‖v‖ < m` and `InjAtLeast hmet p m`, the point `GExp p v` is at distance exactly `‖v‖` from
`p` (the Euclidean distance in the tangent space is the Riemannian distance). -/
theorem ofReal_norm_eq_edist_of_GExp_eq (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m)
    {v : TangentSpace I p} (hv : ‖v‖ < m) :
    Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) = ENNReal.ofReal ‖v‖ := by
  obtain ⟨w, hwG, hwd⟩ :=
    exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p (GExp (cov := cov) hmet p v)
  have hle : ENNReal.ofReal ‖w‖ ≤ ENNReal.ofReal ‖v‖ := by
    rw [← hwd]
    exact Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet v
  have hwlt : ‖w‖ < m :=
    lt_of_le_of_lt ((ENNReal.ofReal_le_ofReal_iff (norm_nonneg v)).mp hle) hv
  have hwv : w = v := hinj w v hwlt hv hwG
  exact hwd.trans (by rw [hwv])

/-- **The exponential map is a bijection from the ball of radius `m` in `T_pM` onto the ball of
radius `m` around `p`** (geodesic polar coordinates). -/
theorem bijOn_GExp_ball (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m) :
    Set.BijOn (fun v : TangentSpace I p => GExp (cov := cov) hmet p v)
      {v : TangentSpace I p | ‖v‖ < m}
      {y : M | Manifold.riemannianEDist I p y < ENNReal.ofReal m} := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    show Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) < ENNReal.ofReal m
    rw [ofReal_norm_eq_edist_of_GExp_eq (cov := cov) hmet htor hinj hv]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg v)).mpr hv
  · intro v hv w hw hvw
    exact hinj v w hv hw hvw
  · intro y hy
    obtain ⟨v, hvlt, hvG⟩ := exists_tangent_of_edist_lt (cov := cov) hmet htor hy
    exact ⟨v, hvlt, hvG⟩

end

end Submission.InjBall
