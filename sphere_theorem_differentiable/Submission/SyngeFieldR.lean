import Submission.ParallelBridge
import Submission.SyngeField

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Synge's input in the room-based language: a smooth, parallel, *periodic* field

`Submission.SyngeField.exists_periodic_parallelField` produces, for a chart-covered geodesic loop of
a simply connected even-dimensional manifold, a `GeodesicCover` and a datum `v ≠ 0` such that the
piecewise parallel field `Submission.ParallelGlobal.parallelField` is **periodic** (the same value at
the two ends of the loop).  `Submission.ParallelRoom.parallelFieldR` is the same field built from the
*room* solutions, which is smooth and parallel along `γ` (`parallelFieldR_spec`); by
`Submission.ParallelRoom.parallelFieldR_eq_parallelField` the two agree.

This module packages the two facts together: the periodic datum of the room-based field, together
with its smoothness and its parallelism along the loop.  This is exactly what the Synge shortening
lemma (`Submission.SyngeShorten.exists_shorter_closed_curve`) consumes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.OrientSign
open Submission.JacobiGlobal

namespace Submission.HolDet

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
variable {γ : ℝ → M}

/-- **THE SYNGE INPUT, room-based form.**  For a `C^∞` geodesic loop with `loopSign = 1` (which
simple connectivity supplies) in *even* dimension there is a `GeodesicCover` of the loop, with the
prescribed partition and charts, and a *non-zero* datum `v` such that the room-based parallel field
`parallelFieldR` is

* smooth along `γ` on the whole loop,
* parallel along `γ` (`∇X = 0`),
* **periodic** (`X (C.c C.N) = X (C.c 0)`). -/
theorem exists_periodic_parallelFieldR (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeov : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hnev : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {P : Partition 0 1} {z : ℕ → M} (hP : IsChartLoop (H := H) P γ z)
    (hloop : γ (P.t P.N) = γ (P.t 0))
    (hvelper : deriv (coordC (I := I) (z := z) (γ := γ) P.N) (P.t P.N)
      = deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0))
    (hloopSign : loopSignOf (I := I) P γ z = 1)
    (hEven : Even (Module.finrank ℝ E)) :
    ∃ (C : Submission.ParallelGlobal.GeodesicCover (I := I) cov γ (P.t 0) (P.t P.N))
      (hN : 0 < C.N) (v : E),
      C.N = P.N ∧ C.c = P.t ∧ C.x = z ∧ v ≠ 0 ∧
      (∀ t ∈ Icc (C.c 0) (C.c C.N),
        SmoothAlongAt (I := I) γ
          (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v) t) ∧
      (∀ t ∈ Icc (C.c 0) (C.c C.N),
        covAlong cov (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v) t = 0) ∧
      Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v (C.c C.N)
        = Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v (C.c 0) := by
  obtain ⟨C, hN, v, hCN, hCc, hCx, hv0, -, hper⟩ :=
    exists_periodic_parallelField (cov := cov) (P := P) (z := z) (γ := γ) hP hγsm.continuous
      isOpen_univ (Set.subset_univ _) hγsm.contMDiffOn (fun t _ => hgeov t) (fun t _ => hnev t)
      hloop hvelper hloopSign hEven hmet htor
  have hspec := Submission.ParallelRoom.parallelFieldR_spec (cov := cov) hmet htor C hN v
    (fun k hk t ht => (hγsm.contMDiffOn).mono (Set.subset_univ _))
    (fun k hk t ht => hnev t)
  have hbridge : ∀ t ∈ Icc (C.c 0) (C.c C.N),
      Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v t
        = Submission.ParallelGlobal.parallelField (cov := cov) htor C hN v t :=
    fun t ht => Submission.ParallelRoom.parallelFieldR_eq_parallelField (cov := cov) htor C hN v ht
  have hle : C.c 0 ≤ C.c C.N :=
    Submission.ParallelGlobal.c_mono_le (cov := cov) C (Nat.zero_le C.N) le_rfl
  have hperR : Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v (C.c C.N)
      = Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v (C.c 0) := by
    rw [hbridge (C.c C.N) ⟨hle, le_rfl⟩, hbridge (C.c 0) ⟨le_rfl, hle⟩]
    exact hper
  have hspec1 : ∀ t ∈ Icc (C.c 0) (C.c C.N),
      SmoothAlongAt (I := I) γ
        (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v) t := by
    rw [C.c_zero, C.c_last]
    exact hspec.1
  have hspec2 : ∀ t ∈ Icc (C.c 0) (C.c C.N),
      covAlong cov (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v) t = 0 := by
    rw [C.c_zero, C.c_last]
    exact hspec.2
  exact ⟨C, hN, v, hCN, hCc, hCx, hv0, hspec1, hspec2, hperR⟩

end

end Submission.HolDet
