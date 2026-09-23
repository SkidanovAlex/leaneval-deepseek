import Submission.Work.ValueClosed.Imports

/-!
# Value-closed geodesic loops: the loop-length functional

This file sets up the area of the subproject `Submission/Work/ValueClosed`:

> close the final glue between the existence theorem for **closed** geodesics
> (`IsClosedGeodesicLoopAt hmet p T γ → 2π/√K ≤ T`, supplied by the sibling subprojects
> `Submission/Work/EvenBound` and `Submission/Work/OddBound`) and the (`value`-closed) statement
> `Submission.XuReduction.PinchedLoopLengthLowerBound` that the reduction of the sphere theorem
> actually consumes.

The notion of a *value-closed geodesic loop* is `Submission.GeodesicLoop.IsGeodesicLoopAt`: a
unit-speed `C^∞` geodesic `γ : ℝ → M` with `γ 0 = γ T = p` and **no** velocity matching at the base
point.

## Contents

* `loopLengthSet hmet` — the set of lengths of value-closed geodesic loops;
* `loopLengthInf hmet` — its infimum `ℓ`, "the length of the shortest value-closed loop";
* the basic API: `loopLengthInf` is a lower bound for the length of every value-closed loop
  (`loopLengthInf_le_of_isGeodesicLoopAt`), and every loop is at least twice the *uniform*
  injectivity radius long, so `ℓ > 0` as soon as some loop exists (`loopLengthInf_pos`);
* `injAllAtLeast_loopLengthInf_div_two` — **the key half of Klingenberg's structure theorem for the
  value-closed predicate**: the uniform injectivity radius of `M` is at least `ℓ/2`.
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

/-- **The set of lengths of value-closed geodesic loops** (Xu's notion,
`Submission.GeodesicLoop.IsGeodesicLoopAt`). -/
def loopLengthSet (hmet : IsMetricCompatible cov) : Set ℝ :=
  {T : ℝ | ∃ (p : M) (γ : ℝ → M),
    Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ}

/-- **The length of the shortest value-closed geodesic loop** of `M`.  It is defined as an infimum
and is *not* assumed to be attained; the attainment is
`Work.ValueClosed.exists_isGeodesicLoopAt_loopLengthInf`. -/
noncomputable def loopLengthInf (hmet : IsMetricCompatible cov) : ℝ :=
  sInf (loopLengthSet (I := I) (cov := cov) hmet)

/-- Membership in `loopLengthSet` is the existence of a value-closed geodesic loop. -/
theorem mem_loopLengthSet_iff {hmet : IsMetricCompatible cov} {T : ℝ} :
    T ∈ loopLengthSet (I := I) (cov := cov) hmet ↔
      ∃ (p : M) (γ : ℝ → M),
        Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ :=
  Iff.rfl

/-- `loopLengthSet` is bounded below by `0`. -/
theorem bddBelow_loopLengthSet (hmet : IsMetricCompatible cov) :
    BddBelow (loopLengthSet (I := I) (cov := cov) hmet) := by
  refine ⟨0, fun T hT => ?_⟩
  obtain ⟨p, γ, hloop⟩ := hT
  exact hloop.1.le

/-- **`loopLengthInf` is a lower bound for the length of every value-closed geodesic loop.** -/
theorem loopLengthInf_le_of_isGeodesicLoopAt (hmet : IsMetricCompatible cov)
    {p : M} {T : ℝ} {γ : ℝ → M}
    (h : Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ) :
    loopLengthInf (I := I) (cov := cov) hmet ≤ T :=
  csInf_le (bddBelow_loopLengthSet (I := I) (cov := cov) hmet) ⟨p, γ, h⟩

/-- **`loopLengthInf` is a lower bound for every element of `loopLengthSet`.** -/
theorem loopLengthInf_le_of_mem {hmet : IsMetricCompatible cov} {T : ℝ}
    (hT : T ∈ loopLengthSet (I := I) (cov := cov) hmet) :
    loopLengthInf (I := I) (cov := cov) hmet ≤ T :=
  csInf_le (bddBelow_loopLengthSet (I := I) (cov := cov) hmet) hT

/-- **Every value-closed geodesic loop is at least twice the uniform injectivity radius long.**
This is the easy half of Klingenberg's structure theorem
(`Submission.GeodesicLoop.IsGeodesicLoopAt.two_mul_le_injAtLeast`) applied to the *uniform* radius
`injSup hmet`. -/
theorem two_mul_injSup_le_of_mem_loopLengthSet (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) {T : ℝ}
    (hT : T ∈ loopLengthSet (I := I) (cov := cov) hmet) :
    2 * Submission.InjSup.injSup hmet ≤ T := by
  obtain ⟨p, γ, hloop⟩ := hT
  exact Submission.GeodesicLoop.IsGeodesicLoopAt.two_mul_le_injAtLeast (I := I) (cov := cov)
    hmet htor hloop
    (Submission.InjRadius.injAtLeast_of_injAllAtLeast (I := I) hmet
      (Submission.InjSup.injAllAtLeast_injSup hmet) p)

/-- **The shortest loop length is positive**, as soon as there is at least one value-closed geodesic
loop: every loop is at least twice the uniform injectivity radius `ρ > 0`
(`Submission.UniformInj.exists_pos_injAllAtLeast`). -/
theorem loopLengthInf_pos (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hne : (loopLengthSet (I := I) (cov := cov) hmet).Nonempty) :
    0 < loopLengthInf (I := I) (cov := cov) hmet := by
  obtain ⟨ρ, hρpos, hρall⟩ :=
    Submission.UniformInj.exists_pos_injAllAtLeast (I := I) (cov := cov) hmet
  refine lt_of_lt_of_le (by linarith)
    (le_csInf hne (fun T hT => ?_))
  obtain ⟨p, γ, hloop⟩ := hT
  have h2 : 2 * ρ ≤ T :=
    Submission.GeodesicLoop.IsGeodesicLoopAt.two_mul_le_injAtLeast (I := I) (cov := cov) hmet
      htor hloop (hρall p)
  linarith

/-- **The key half of Klingenberg's structure theorem for the value-closed predicate.**

The uniform injectivity radius of `M` is at least half the length of the shortest value-closed
geodesic loop: `InjAllAtLeast hmet (ℓ/2)`.

*Proof.*  Let `z ∈ M` and let `m` be the *maximal* injectivity radius at `z`
(`Submission.InjRadius.exists_injAtLeast_max`).  If `m ≥ ℓ/2` we are done by monotonicity, so
suppose `m < ℓ/2 < π/√K`.  The cut-point step
(`Submission.RayConj.exists_two_minimising_of_injAtLeast_of_lt_pi_div_sqrt`) produces two distinct
minimising vectors `u ≠ v` of norm `m` with the same image, and the (proved) Klingenberg–Xu step
(`Submission.XuReduction.klingenbergLoopStep`) turns them into a value-closed geodesic loop at `z` of
length `≤ 2m < ℓ` — contradicting the definition of `ℓ` as the infimum. -/
theorem injAllAtLeast_loopLengthInf_div_two (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hcurv : Submission.RauchK.CurvLe cov K) (hKpos : 0 < K)
    (hℓπ : loopLengthInf (I := I) (cov := cov) hmet / 2 < Real.pi / Real.sqrt K) :
    InjAllAtLeast hmet (loopLengthInf (I := I) (cov := cov) hmet / 2) := by
  intro z
  by_cases htriv : loopLengthInf (I := I) (cov := cov) hmet / 2 ≤ 0
  · exact Submission.InjRadius.injAtLeast_mono (I := I) hmet
      (Submission.InjSup.injAtLeast_zero hmet z) htriv
  · push Not at htriv
    by_contra hz
    obtain ⟨ρ, hρpos, hρall⟩ :=
      Submission.UniformInj.exists_pos_injAllAtLeast (I := I) (cov := cov) hmet
    obtain ⟨R, -, hR⟩ := Submission.CutTime.exists_edist_le (I := I) (cov := cov) hmet htor z
    obtain ⟨m, hm_inj, hm_max⟩ :=
      Submission.InjRadius.exists_injAtLeast_max (I := I) (cov := cov) hmet
        ⟨ρ, hρall z⟩
        ⟨max R 0 + 2, Submission.InjSup.not_injAtLeast_of_lt_diam (I := I) (cov := cov) hmet
          htor (x := z) (D := R) (s := max R 0 + 1)
          (by have h : (0:ℝ) ≤ max R 0 := le_max_right R 0; linarith)
          (by have h : R ≤ max R 0 := le_max_left R 0; linarith) hR (by linarith)⟩
    have hm_lt : m < loopLengthInf (I := I) (cov := cov) hmet / 2 := by
      by_contra hge
      push Not at hge
      exact hz (Submission.InjRadius.injAtLeast_mono (I := I) hmet hm_inj hge)
    have hmπ : m < Real.pi / Real.sqrt K := by linarith
    have hmpos : 0 < m := by
      have : ρ ≤ m := le_of_not_gt fun hlt => hm_max ρ hlt (hρall z)
      linarith
    obtain ⟨u, v, huv, hG, hu, hv, -⟩ :=
      Submission.RayConj.exists_two_minimising_of_injAtLeast_of_lt_pi_div_sqrt (cov := cov)
        hmet htor hcurv hKpos hmpos hmπ hm_inj hm_max
    obtain ⟨T, γ, hTle, hloop⟩ :=
      Submission.XuReduction.klingenbergLoopStep (I := I) (cov := cov) hmet htor hcurv hKpos
        z hmpos hm_inj hm_max hmπ u v huv hu hv hG
    have h1 : loopLengthInf (I := I) (cov := cov) hmet ≤ T :=
      loopLengthInf_le_of_isGeodesicLoopAt (I := I) (cov := cov) hmet hloop
    linarith

end

end Work.ValueClosed
