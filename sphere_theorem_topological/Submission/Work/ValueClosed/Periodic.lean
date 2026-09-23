import Submission.Work.ValueClosed.Defs

/-!
# From a periodic ray to a closed geodesic loop, and the limit step of the minimiser

Two shape lemmas used by the final assembly `Work.ValueClosed.pinched_loop_length_lower_bound`:

* `isClosedGeodesicLoopAt_of_ray_periodic` — a `GExp`-ray that is periodic of period `2m` is a
  **closed** geodesic loop (velocity matched) of length `2m`, i.e. a
  `Submission.KlingenbergLemma.IsClosedGeodesicLoopAt` — the object the Klingenberg length bound
  `hclosed` of the sibling subprojects applies to;
* `GExp_return_of_raySeq_tendsto` — the limit step of the existence of the shortest value-closed
  loop: if a family of `GExp`-rays with unit directions and lengths `L n → L > 0` returns to its base
  points, then so does the limit ray.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius

namespace Work.ValueClosed

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

/-- **A periodic `GExp`-ray is a closed geodesic loop.**  Let `ξ` be a unit tangent vector at `p`
whose ray is periodic of period `2m` with `m > 0`: `GExp p ((u + 2m) • ξ) = GExp p (u • ξ)` for all
`u`.  Then `s ↦ GExp p (s • ξ)` is a unit-speed `C^∞` geodesic on `ℝ` with `γ 0 = γ (2m) = p` and
**matching velocities** at the two ends, i.e. a `Submission.KlingenbergLemma.IsClosedGeodesicLoopAt`
of length `2m` — a genuine closed geodesic. -/
theorem isClosedGeodesicLoopAt_of_ray_periodic (hmet : IsMetricCompatible cov)
    {p : M} {m : ℝ} {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hm : 0 < m)
    (hper : ∀ u : ℝ,
      GExp (cov := cov) hmet p ((u + 2 * m) • ξ) = GExp (cov := cov) hmet p (u • ξ)) :
    Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p (2 * m)
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) := by
  have hξne : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ
    norm_num at hξ
  have hmd : ∀ t : ℝ, MDifferentiableAt 𝓘(ℝ) I
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t := fun t =>
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξne).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by simp)
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show GExp (cov := cov) hmet p ((0 : ℝ) • ξ) = p
    rw [zero_smul, GExp_zero]
  · show GExp (cov := cov) hmet p ((2 * m) • ξ) = p
    have h := hper 0
    rw [zero_add, zero_smul, GExp_zero] at h
    exact h
  · exact Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξne
  · intro t
    exact Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne t
  · intro t
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t]
    rw [Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hξne t]
    exact hξ
  · -- velocity matching, from the periodicity of the ray
    have hσ : (fun u : ℝ => GExp (cov := cov) hmet p ((u + 2 * m) • ξ))
        = (fun u : ℝ => GExp (cov := cov) hmet p (u • ξ)) := funext hper
    have hv1 : curveVelocity (I := I)
        (fun u : ℝ => GExp (cov := cov) hmet p ((u + 2 * m) • ξ)) 0
        = curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (2 * m) := by
      have hfun : (fun u : ℝ => GExp (cov := cov) hmet p ((u + 2 * m) • ξ))
          = (fun u : ℝ => (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (1 * u + 2 * m)) := by
        funext u
        rw [one_mul]
      rw [hfun]
      rw [Submission.Length.curveVelocity_comp_mul_add (I := I)
        (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (c := 1) (d := 2 * m) (t := 0)
        (hmd (1 * 0 + 2 * m))]
      rw [show (1 : ℝ) * 0 + 2 * m = 2 * m from by ring, one_smul]
    rw [← hv1, hσ]

/-- **The limit step of the existence of the shortest value-closed loop.**  Let `z₀` be a chart
centre, `pstar` a point of its chart source, `q n → pstar`, `y n → y₀` chart coordinates of unit
directions, `L n → L` with `L > 0` and `L n ≥ 0`.  If each ray returns to its base point at time
`L n`, then the limit ray returns at time `L`:
`GExp pstar (L • frameVector z₀ pstar y₀) = pstar`. -/
theorem GExp_return_of_raySeq_tendsto (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {pstar : M} (hpstar : pstar ∈ (chartAt H z₀).source)
    {q : ℕ → M} (hq : Tendsto q atTop (𝓝 pstar))
    {y : ℕ → E} {y₀ : E} (hy : Tendsto y atTop (𝓝 y₀))
    (hunit : ∀ n, ‖frameVector (I := I) z₀ (q n) (y n)‖ = 1)
    (hu₀ : ‖frameVector (I := I) z₀ pstar y₀‖ = 1)
    {Ln : ℕ → ℝ} {L : ℝ} (hLn : Tendsto Ln atTop (𝓝 L)) (hLnpos : ∀ n, 0 ≤ Ln n)
    (hL : 0 < L)
    (hret : ∀ n, GExp (cov := cov) hmet (q n) (Ln n • frameVector (I := I) z₀ (q n) (y n))
      = q n) :
    GExp (cov := cov) hmet pstar (L • frameVector (I := I) z₀ pstar y₀) = pstar := by
  have h2 := Submission.GExpJointPt.tendsto_GExp_ray_length (cov := cov) hmet htor hpstar hq hy
    hunit hu₀ hLn hLnpos hL
  have hev : (fun n => Submission.GExpJointPt.raySeq (cov := cov) hmet z₀ q y (Ln n) n)
      =ᶠ[atTop] q := Filter.Eventually.of_forall fun n => hret n
  have h3 : Tendsto (fun n => Submission.GExpJointPt.raySeq (cov := cov) hmet z₀ q y (Ln n) n)
      atTop (𝓝 pstar) := (Filter.tendsto_congr' hev).mpr hq
  exact tendsto_nhds_unique h2 h3

end

end Work.ValueClosed
