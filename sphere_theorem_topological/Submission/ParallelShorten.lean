import Submission.ParallelRoom
import Submission.EnergyShorten
import Submission.GExpRayZero

/-!
# The shortening of a geodesic by a parallel field, instantiated for `GExp`-rays

This file closes item 1 of `Submission/Roadmap.lean` §113.3bis / §114.5: the abstract shortening
theorem `Submission.EnergyShorten.exists_curveLength_lt_of_positive_curvature` is instantiated with
the **global parallel field** `Submission.ParallelRoom.parallelFieldR`.

* **`exists_geodesicCover_ray`** — the `GExp`-ray `s ↦ GExp p (s • ξ)` (`ξ ≠ 0`) admits a
  `GeodesicCover` over any interval (its smoothness is global,
  `Submission.ConjEnergy.contMDiff_GExp_smul`, and it is a geodesic at every parameter,
  `Submission.GExpRayZero.isGeodesicAt_GExp_smul_all`);
* **`exists_curveLength_lt_of_parallelFieldR`** — **the Synge shortening**: for a unit-speed
  `GExp`-ray of length `L > 0` and a datum `v₀` whose parallel extension `V` has *positive curvature
  pairing* on `[0,L]`, there is `d > 0` such that the curves `t ↦ GExp (γ t) (σ • (d • V t))` have
  length `< L` for all small `σ` on one side of `0`.

This is exactly what the even-dimensional case of Klingenberg's estimate consumes, once Synge's
lemma provides the *closed* parallel unit normal field whose curvature pairing is `sec > 0`.
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
open Submission.JacobiGlobal
open Submission.GlobalExp
open Submission.Length
open Submission.CurvatureVec

namespace Submission.ParallelShorten

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

/-- **The `GExp`-ray admits a chart cover over any interval.** -/
theorem exists_geodesicCover_ray (hmet : IsMetricCompatible cov) {p : M} {ξ : TangentSpace I p}
    (hξ : ξ ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    Nonempty (Submission.ParallelGlobal.GeodesicCover cov
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) a b) :=
  Submission.ParallelGlobal.exists_geodesicCover (cov := cov)
    (V := (univ : Set ℝ)) isOpen_univ hab (fun _ _ => mem_univ _)
    ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hξ).contMDiffOn)
    (fun t _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξ t)
    (fun t _ => Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hξ t)

/-- **THE SYNGE SHORTENING, instantiated.**  For a unit-speed `GExp`-ray of length `L > 0` and a
datum `v₀` whose parallel extension along the ray has positive curvature pairing on `[0,L]`, the
family of curves `t ↦ GExp (γ t) (σ • (d • V t))` is strictly shorter than the ray itself for all
small `σ` on one side of `0`. -/
theorem exists_curveLength_lt_of_parallelFieldR (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0) (hξ1 : ‖ξ‖ = 1)
    {L : ℝ} (hL : 0 < L)
    (C : Submission.ParallelGlobal.GeodesicCover cov
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (0 - 1) (L + 1))
    (hN : 0 < C.N) (v₀ : E)
    (hpos : ∀ t ∈ Icc (0 : ℝ) L, 0 < inner ℝ
      (curvVec cov (GExp (cov := cov) hmet p (t • ξ))
        (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₀ t)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t))
      (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₀ t)) :
    ∃ d : ℝ, 0 < d ∧
      ((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
            (GExp (cov := cov) hmet p (t • ξ))
            (σ • (d • Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₀ t))) 0 L < L) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
            (GExp (cov := cov) hmet p (t • ξ))
            (σ • (d • Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₀ t))) 0 L < L)) := by
  have hspec := Submission.ParallelRoom.parallelFieldR_spec (cov := cov) hmet htor C hN v₀
    (fun k hk t ht => (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hξ).contMDiffOn)
    (fun k hk t ht => Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hξ t)
  exact Submission.EnergyShorten.exists_curveLength_lt_of_positive_curvature (cov := cov) hmet htor
    hξ hξ1 hspec.1 hspec.2 hL hpos

end

end Submission.ParallelShorten
