import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.OddBound.Assembly
import Submission.Work.EvenBound.EvenBound
import Submission.Work.OddBound.assembly.MinimaxExtraction
import Submission.Work.OddBound.Minimax

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric
open Submission.CurvatureVec

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Bridge

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **`Pinched` at a point.**  If the curvature of `cov` is `(κ, Λ]`-pinched (in the sense of
`Submission.Diff.Pinched`, i.e. tested on globally smooth unit fields), then for every point `x`
and every *pointwise* orthonormal pair `u, v` the sectional numerator
`⟪R(u,v)v, u⟫` lies in `(κ, Λ]`.  The bridge is
`Submission.CurvatureVec.curvVec_eq`, which identifies the extension-defined `curvVec` with
`curv` evaluated on the chosen smooth extensions. -/
theorem pinched_curvVec_bounds {κ Λ : ℝ} (hpinch : Pinched cov κ Λ) (x : M)
    (u v : TangentSpace I x) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    κ < inner ℝ (curvVec cov x u v v) u ∧ inner ℝ (curvVec cov x u v v) u ≤ Λ := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  have h1 : inner ℝ (X x) (X x) = 1 := by
    rw [hXx, real_inner_self_eq_norm_sq, hu]
    norm_num
  have h2 : inner ℝ (Y x) (Y x) = 1 := by
    rw [hYx, real_inner_self_eq_norm_sq, hv]
    norm_num
  have h3 : inner ℝ (X x) (Y x) = 0 := by
    rw [hXx, hYx]
    exact huv
  have hp := hpinch X Y hX hY x h1 h2 h3
  rw [curvVec_eq cov (inferInstance : ContMDiffCovariantDerivative cov ∞) hX hY hY hXx hYx hYx,
    ← hXx]
  exact hp

-- (Named `curvLe_of_pinched_v2` rather than `curvLe_of_pinched`, which is declared in
-- `Submission.Work.Diff.C.HessLowerAux`: two modules declaring the same name cannot be imported
-- together.)
/-- The pointwise upper curvature bound `sec ≤ Λ` in the form `Submission.RauchK.CurvLe`. -/
theorem curvLe_of_pinched_v2 {κ Λ : ℝ} (hpinch : Pinched cov κ Λ) :
    Submission.RauchK.CurvLe cov Λ :=
  fun x u v hu hv huv => (pinched_curvVec_bounds (I := I) (cov := cov) hpinch x u v hu hv huv).2

/-- The pointwise strict lower curvature bound `κ < sec`. -/
theorem lt_of_pinched {κ Λ : ℝ} (hpinch : Pinched cov κ Λ) (x : M)
    (u v : TangentSpace I x) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    κ < inner ℝ (curvVec cov x u v v) u :=
  (pinched_curvVec_bounds (I := I) (cov := cov) hpinch x u v hu hv huv).1

end Bridge

-- ROUTE.  This isolates the Klingenberg injectivity-radius input of area C
-- (`Work.Diff.C.dist_eikonal2`, dormant), so that it can be discharged from the Klingenberg
-- machinery that is ALREADY PROVED in this workspace.
-- STEP 1.  `Pinched cov 1 (1+η)` gives, on smooth unit vector fields `X ⟂ Y`,
-- `1 < inner ℝ (curv cov X Y Y x) (X x) ≤ 1 + η`.  Put `K := 1 + η` (so `0 < K < 4` since
-- `η < 3`).  Two consequences to extract with `hmet`/`htor`:
--   (a) `Submission.RauchK.CurvLe cov K`: need `inner ℝ (curvVec cov p u v v) u ≤ K` for
--       orthonormal `u,v`; `curvVec` and `curv` agree for smooth fields (see
--       `Submission/CurvatureVec.lean`, `Submission/Curvature.lean`).  See also the scratch
--       `_chk_pp.lean` in the workspace root, which sketches the `Pinched`-to-pointwise bridge
--       (`pinched_pointwise`) that the reviewers flagged as the only real work here.
--   (b) the pointwise quarter pinching `∀ p u v, ‖u‖ = 1 → ‖v‖ = 1 → ⟪u,v⟫ = 0 →
--       K / 4 + ε ≤ inner ℝ (curvVec cov p u v v) u` with `ε := (3 - η) / 4 > 0`: this is
--       `1 ≥ (1+η)/4 + (3-η)/4 = 1`, using only `1 < sec`.
--       (For the even case the weaker `K/4 ≤ sec` suffices.)
-- STEP 2 (parity split; `hdim` rules out `finrank = 1`).
--   * `Module.finrank ℝ E` EVEN:
--       `Work.EvenBound.injAllAtLeast_pi_div_sqrt_even`
--       (`Submission/Work/EvenBound/EvenBound.lean`, sorry-free): with `hmet`, `htor`,
--       `[PathConnectedSpace M]`, `[RegularSpace M]`, `[SimplyConnectedSpace M]`, `Even`, `0 < K`,
--       `Submission.RauchK.CurvLe cov K` and `K/4 ≤ sec`, it gives exactly
--       `InjAllAtLeast hmet (π/√K)`.
--   * `Module.finrank ℝ E` ODD: `hdim` + odd gives `3 ≤ finrank`, so
--       `Work.OddBound.injAllAtLeast_pi_div_sqrt_odd_of_minimaxInput`
--       (`Submission/Work/OddBound/Minimax.lean`, sorry-free) applies once `MinimaxInput` is
--       supplied; `MinimaxInput (I:=I) (cov:=cov) hmet htor K` follows from
--       `Work.OddBound.minimaxInput_of_extraction_and_lhl`
--       (`Submission/Work/OddBound/Assembly.lean`) with the minimax extraction
--       `Work.OddBound.assembly.MinimaxExtraction` — which is PROVED in
--       `Submission/Work/OddBound/assembly/MinimaxExtraction.lean` (the whole `Work/OddBound` tree
--       has no `sorry`).
-- `[PathConnectedSpace M]` and `[RegularSpace M]` are NOT hypotheses: they follow from
-- `[SimplyConnectedSpace M]` and from `[CompactSpace M] [T2Space M]` respectively (use `haveI`).
-- NOTE `Real.pi / Real.sqrt (1 + η)` is `Real.pi / Real.sqrt K` definitionally.
theorem inj_radius_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {η : ℝ} (hη : 0 < η) (hη3 : η < 3) (hpinch : Pinched cov 1 (1 + η)) :
    Submission.InjRadius.InjAllAtLeast (I := I) (cov := cov) hmet
      (Real.pi / Real.sqrt (1 + η)) := by
  classical
  -- `M` is path connected (simply connected) and regular (compact Hausdorff).
  haveI : PathConnectedSpace M := inferInstance
  haveI : RegularSpace M := inferInstance
  -- ## STEP 1: pointwise curvature bounds
  have hlt : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      (1 : ℝ) < inner ℝ (curvVec cov p u v v) u :=
    fun p u v hu hv huv => lt_of_pinched (I := I) (cov := cov) hpinch p u v hu hv huv
  have hcurv : Submission.RauchK.CurvLe cov (1 + η) :=
    curvLe_of_pinched_v2 (I := I) (cov := cov) hpinch
  have hKpos : (0 : ℝ) < 1 + η := by linarith
  -- the weak quarter pinching `K/4 ≤ sec` for the even case
  have hpinchEven : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      (1 + η) / 4 ≤ inner ℝ (curvVec cov p u v v) u := by
    intro p u v hu hv huv
    have h := hlt p u v hu hv huv
    have h4 : (1 + η) / 4 ≤ 1 := by linarith
    linarith
  -- the strict quarter pinching `K/4 + ε ≤ sec`, `ε = (3-η)/4`, for the odd case
  have hpinchOdd : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      (1 + η) / 4 + (3 - η) / 4 ≤ inner ℝ (curvVec cov p u v v) u := by
    intro p u v hu hv huv
    have h := hlt p u v hu hv huv
    have h4 : (1 + η) / 4 + (3 - η) / 4 = 1 := by ring
    linarith
  -- ## STEP 2: parity split
  rcases Nat.even_or_odd (Module.finrank ℝ E) with hEven | hOdd
  · -- EVEN dimension
    exact Work.EvenBound.injAllAtLeast_pi_div_sqrt_even (I := I) (cov := cov) hmet htor hEven
      hKpos hcurv hpinchEven
  · -- ODD dimension: `hdim` plus oddness forces `3 ≤ finrank`
    have hDim : 3 ≤ Module.finrank ℝ E := by
      obtain ⟨k, hk⟩ := hOdd
      omega
    have hε : (0 : ℝ) < (3 - η) / 4 := by linarith
    have hext : Work.OddBound.MinimaxExtraction (I := I) (cov := cov) hmet htor (1 + η) :=
      Work.OddBound.minimaxExtraction (I := I) (cov := cov) hmet htor
    have hminimax : Work.OddBound.MinimaxInput (I := I) (cov := cov) hmet htor (1 + η) :=
      Work.OddBound.minimaxInput_of_extraction_and_lhl (I := I) (cov := cov) hmet htor hKpos
        hcurv hext
    exact Work.OddBound.injAllAtLeast_pi_div_sqrt_odd_of_minimaxInput (I := I) (cov := cov)
      hmet htor hDim hKpos hε hcurv hpinchOdd hminimax

end Work.Diff.C
