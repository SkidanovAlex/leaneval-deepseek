import Submission.HolSynge
import Submission.ParallelGlobal
import Submission.GeodesicGlobal
import Submission.CurveField
import Submission.SecondVarGlobal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Synge input of the even-dimensional Klingenberg estimate, from intrinsic geodesic data

This module turns the abstract combinatorial statement `Submission.HolDet.exists_fixed_normal_coord`
(into which `Submission.HolSynge` feeds the isometry, the determinant and the velocity) into a
statement whose hypotheses are the *geometric* ones of a closed geodesic.  See Roadmap §122.

* `hasDerivAt_chartODE_of_isGeodesic` — the chart geodesic equation at a single time, for a `C^∞`
  intrinsic geodesic on an open set `V` (`HasDerivAt` is a germ condition, so no covering argument
  is needed: the global smooth section of the velocity is produced locally by
  `CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity`);
* `exists_Ioo_subset_of_Icc_subset_isOpen`, `exists_room_of_isChartLoop` — the room of a chart cover;
* `chartData_of_isChartLoop` — the analytic chart data of a chart-covered geodesic;
* `exists_fixed_normal_coord_of_isGeodesic`, `exists_fixed_normal_coord_of_isChartLoop` — the Synge
  input with `hgeo` replaced by intrinsic geodesicity on an open set `V`.

`exists_room_of_isChartLoop` and `hasDerivAt_chartODE_of_isGeodesic` are also the two ingredients of
the `ParallelGlobal.GeodesicCover` with **prescribed** partition and charts (Roadmap §122.5).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiTensor
open Submission.OrientSign
open Submission.ChartConnection
open Submission.BonnetMyers
open Submission.Jacobi

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

/-- **The chart geodesic equation at a single time**, for an intrinsic geodesic: the chart
coordinate curve in the chart at `x₀` is differentiable at `t₀` with derivative its `deriv`, and its
`deriv` satisfies the chart geodesic equation at `t₀`. -/
theorem hasDerivAt_chartODE_of_isGeodesic {x₀ : M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ}
    (ht₀ : t₀ ∈ V) (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hsrc : γ t₀ ∈ (chartAt H x₀).source)
    (hgeo : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0) :
    HasDerivAt (fun t : ℝ => (extChartAt I x₀) (γ t))
        (deriv (fun t : ℝ => (extChartAt I x₀) (γ t)) t₀) t₀ ∧
      HasDerivAt (deriv (fun t : ℝ => (extChartAt I x₀) (γ t)))
        (chartGeodesicVectorField cov x₀
          ((extChartAt I x₀) (γ t₀),
            deriv (fun t : ℝ => (extChartAt I x₀) (γ t)) t₀)) t₀ := by
  obtain ⟨Z, hZ, hZeq⟩ :=
    Submission.CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity
      (I := I) hV ht₀ hγ (hne t₀ ht₀)
  obtain ⟨δ, hδ, -, -, h3, h4⟩ :=
    Submission.GeodesicGlobal.chartODE_of_isGeodesic (cov := cov) x₀ hV ht₀ hγ hsrc
      (fun s hs => hgeo s hs) Z hZ hZeq
  exact ⟨h3 t₀ ⟨by linarith, by linarith⟩, h4 t₀ ⟨by linarith, by linarith⟩⟩


/-- **A compact interval inside an open set has room**: `Icc a b ⊆ s` with `s` open gives
`Ioo A B ⊆ s` with `A < a` and `b < B`. -/
theorem exists_Ioo_subset_of_Icc_subset_isOpen {s : Set ℝ} (hs : IsOpen s) {a b : ℝ}
    (hab : a ≤ b) (hsub : Icc a b ⊆ s) :
    ∃ A B : ℝ, A < a ∧ b < B ∧ Ioo A B ⊆ s := by
  obtain ⟨δ, hδ, hδsub⟩ := isCompact_Icc.exists_cthickening_subset_open hs hsub
  refine ⟨a - δ / 2, b + δ / 2, by linarith, by linarith, fun t ht => hδsub ?_⟩
  have hle : dist t (max a (min t b)) ≤ δ / 2 := by
    have hy1 : max a (min t b) ≤ t + δ / 2 := by
      have h1 : max a (min t b) ≤ max a t :=
        max_le (le_max_left _ _) (le_trans (min_le_left _ _) (le_max_right _ _))
      have h2 : max a t ≤ t + δ / 2 := max_le (by linarith [ht.1]) (by linarith)
      linarith
    have hy2 : t ≤ max a (min t b) + δ / 2 := by
      rcases le_or_gt t b with htb | htb
      · have h1 : min t b = t := min_eq_left htb
        rw [h1]
        linarith [le_max_right a t]
      · have h1 : min t b = b := min_eq_right htb.le
        have h2 : max a (min t b) = b := by rw [h1, max_eq_right hab]
        rw [h2]
        linarith [ht.2]
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  exact mem_cthickening_of_dist_le t (max a (min t b)) δ (Icc a b)
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩ (by linarith)


/-- **The chart geodesic equation on the closed piece, from intrinsic geodesicity.**  The hypotheses
of `exists_fixed_normal_coord` that involve taking a second derivative are derived here from the
assumption that `γ` is an intrinsic geodesic on the open set `V` (which contains `[P.t 0, P.t P.N]`):
`chartODE_of_isGeodesic` + `CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity` give the
equation at every single time, and a `HasDerivAt` statement is a germ condition, so no covering
argument is needed. -/
theorem hasDerivAt_chartGeo_of_isChartLoop {P : Partition 0 1} {z : ℕ → M} {γ : ℝ → M}
    (hP : IsChartLoop (H := H) P γ z) {V : Set ℝ} (hV : IsOpen V)
    (hVsub : Icc (P.t 0) (P.t P.N) ⊆ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeov : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hnev : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0) :
    (∀ k < P.N, ∀ t ∈ Ioo (P.t k) (P.t (k+1)),
      HasDerivAt (coordC (I := I) (z := z) (γ := γ) k) (deriv (coordC (I := I) (z := z) (γ := γ) k) t) t) ∧
    (∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      HasDerivAt (deriv (coordC (I := I) (z := z) (γ := γ) k))
        (chartGeodesicVectorField cov (z k)
          (coordC (I := I) (z := z) (γ := γ) k t,
            deriv (coordC (I := I) (z := z) (γ := γ) k) t)) t) := by
  constructor
  · intro k hk t ht
    have htV : t ∈ V := hVsub ⟨le_trans (P.mono_le (Nat.zero_le k) hk.le) ht.1.le,
      le_trans ht.2.le (P.mono_le (by omega) le_rfl)⟩
    have hsrc : γ t ∈ (chartAt H (z k)).source := hP.1 k hk t ⟨ht.1.le, ht.2.le⟩
    exact (hasDerivAt_chartODE_of_isGeodesic (cov := cov) (x₀ := z k) hV htV hγ hsrc
      hgeov hnev).1
  · intro k hk t ht
    have htV : t ∈ V := hVsub ⟨le_trans (P.mono_le (Nat.zero_le k) hk.le) ht.1,
      le_trans ht.2 (P.mono_le (by omega) le_rfl)⟩
    have hsrc : γ t ∈ (chartAt H (z k)).source := hP.1 k hk t ht
    exact (hasDerivAt_chartODE_of_isGeodesic (cov := cov) (x₀ := z k) hV htV hγ hsrc
      hgeov hnev).2

/-- **`exists_fixed_normal_coord` with the second-derivative hypotheses replaced by intrinsic
geodesicity.** -/
theorem exists_fixed_normal_coord_of_isGeodesic {P : Partition 0 1} {z : ℕ → M} {γ : ℝ → M}
    (hP : IsChartLoop (H := H) P γ z) (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdiff : ∀ k < P.N, ∀ t ∈ Ioo (P.t k) (P.t (k+1)),
      HasDerivAt (coordC (I := I) (z := z) (γ := γ) k) (deriv (coordC (I := I) (z := z) (γ := γ) k) t) t)
    (hγcont : ContinuousOn γ (Icc (P.t 0) (P.t P.N)))
    (hsrc : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (hγmd : ∀ t ∈ Icc (P.t 0) (P.t P.N), MDifferentiableAt 𝓘(ℝ) I γ t)
    {V : Set ℝ} (hV : IsOpen V) (hVsub : Icc (P.t 0) (P.t P.N) ⊆ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeov : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hnev : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0)
    (hloop : γ (P.t P.N) = γ (P.t 0))
    (hvelper : deriv (coordC (I := I) (z := z) (γ := γ) P.N) (P.t P.N)
      = deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0))
    (hloopSign : loopSignOf (I := I) P γ z = 1)
    (hvelne : deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0) ≠ 0)
    (hEven : Even (Module.finrank ℝ E)) :
    ∃ v : E, v ≠ 0
      ∧ chartGram (I := I) (z 0) (γ (P.t 0))
          (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0)) v = 0
      ∧ holAux (cov := cov) htor hu hw htgt P.N v = v :=
  exists_fixed_normal_coord (cov := cov) (P := P) (z := z) (γ := γ) hP hmet hdiff hγcont hsrc
    (hasDerivAt_chartGeo_of_isChartLoop (cov := cov) hP hV hVsub hγ hgeov hnev).2
    hγmd htor hu hw htgt hloop hvelper hloopSign hvelne hEven


/-- **The room of a chart-covered curve.**  A chart-covered curve has, for every piece, an open
interval `Ioo (A k) (B k)` strictly containing `[P.t k, P.t (k+1)]`, on which the chart `z k` is valid
and which stays inside `V`.  (Openness of the chart source + continuity of `γ` at the two endpoints +
`exists_Ioo_subset_of_Icc_subset_isOpen`.) -/
theorem exists_room_of_isChartLoop {P : Partition 0 1} {z : ℕ → M} {γ : ℝ → M}
    (hP : IsChartLoop (H := H) P γ z) (hγc : Continuous γ) {V : Set ℝ} (hV : IsOpen V)
    (hVsub : Icc (P.t 0) (P.t P.N) ⊆ V) :
    ∃ A B : ℕ → ℝ, (∀ k < P.N, A k < P.t k ∧ P.t (k+1) < B k) ∧
      (∀ k < P.N, Ioo (A k) (B k) ⊆ V) ∧
      (∀ k < P.N, ∀ t ∈ Ioo (A k) (B k), γ t ∈ (chartAt H (z k)).source) := by
  have hroom : ∀ k : ℕ, ∃ A B : ℝ, k < P.N → A < P.t k ∧ P.t (k+1) < B ∧ Ioo A B ⊆ V ∧
      (∀ t ∈ Ioo A B, γ t ∈ (chartAt H (z k)).source) := by
    intro k
    by_cases hk : k < P.N
    · have hsub : Icc (P.t k) (P.t (k+1)) ⊆ V := fun t ht =>
        hVsub ⟨le_trans (P.mono_le (Nat.zero_le k) hk.le) ht.1,
          le_trans ht.2 (P.mono_le (by omega) le_rfl)⟩
      have hsrc : Icc (P.t k) (P.t (k+1)) ⊆ γ ⁻¹' (chartAt H (z k)).source :=
        fun t ht => hP.1 k hk t ht
      obtain ⟨A, B, hA, hB, hABsub⟩ := exists_Ioo_subset_of_Icc_subset_isOpen
        (hV.inter ((chartAt H (z k)).open_source.preimage hγc)) (P.mono k hk).le
        (fun t ht => ⟨hsub ht, hsrc ht⟩)
      exact ⟨A, B, fun _ => ⟨hA, hB, fun t ht => (hABsub ht).1, fun t ht => (hABsub ht).2⟩⟩
    · exact ⟨0, 1, fun h => absurd h hk⟩
  choose A B hAB using hroom
  exact ⟨A, B, fun k hk => ⟨(hAB k hk).1, (hAB k hk).2.1⟩, fun k hk => (hAB k hk).2.2.1,
    fun k hk t ht => (hAB k hk).2.2.2 t ht⟩

/-- **The chart data of a chart-covered geodesic.**  All the "analytic" hypotheses of
`exists_fixed_normal_coord` (continuity of the coordinate curve and of its derivative, target
membership, differentiability of the coordinate curve, continuity and differentiability of `γ`) are
produced here from `IsChartLoop P γ z`, the global continuity of `γ`, and the smoothness and
geodesicity of `γ` on an open set `V ⊇ [P.t 0, P.t P.N]`.

The room `Ioo (A k) (B k) ⊇ [P.t k, P.t (k+1)]` on which the chart `z k` is valid is produced by
`exists_Ioo_subset_of_Icc_subset_isOpen`; the differential statements are `ContDiffOn`-consequences
of smoothness on the room, and target membership is `PartialEquiv.map_source`. -/
theorem chartData_of_isChartLoop {P : Partition 0 1} {z : ℕ → M} {γ : ℝ → M}
    (hP : IsChartLoop (H := H) P γ z) (hγc : Continuous γ) {V : Set ℝ} (hV : IsOpen V)
    (hVsub : Icc (P.t 0) (P.t P.N) ⊆ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeov : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hnev : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0) :
    (∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source) ∧
    (∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1)))) ∧
    (∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1)))) ∧
    (∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target) ∧
    (∀ k < P.N, ∀ t ∈ Ioo (P.t k) (P.t (k+1)),
      HasDerivAt (coordC (I := I) (z := z) (γ := γ) k)
        (deriv (coordC (I := I) (z := z) (γ := γ) k) t) t) ∧
    ContinuousOn γ (Icc (P.t 0) (P.t P.N)) ∧
    (∀ t ∈ Icc (P.t 0) (P.t P.N), MDifferentiableAt 𝓘(ℝ) I γ t) := by
  have hle_infty : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    show ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  obtain ⟨A, B, hAB, hroomV, hroomsrc⟩ :=
    exists_room_of_isChartLoop hP hγc hV hVsub

  have hcoord : ∀ k, k < P.N → ContDiffOn ℝ (∞ : ℕ∞ω) (coordC (I := I) (z := z) (γ := γ) k)
      (Ioo (A k) (B k)) := by
    intro k hk
    exact Submission.SecondVarGlobal.contDiffOn_chartCoord (I := I) (z₀ := z k)
      (hγ.mono (hroomV k hk)) (fun t ht => hroomsrc k hk t ht)
  have hpiece : ∀ k, k < P.N → Icc (P.t k) (P.t (k+1)) ⊆ Ioo (A k) (B k) := fun k hk t ht =>
    ⟨lt_of_lt_of_le (hAB k hk).1 ht.1, lt_of_le_of_lt ht.2 (hAB k hk).2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun k hk t ht => hP.1 k hk t ht
  · intro k hk
    exact ((hcoord k hk).continuousOn).mono (hpiece k hk)
  · intro k hk
    exact ((hcoord k hk).continuousOn_deriv_of_isOpen isOpen_Ioo hle_infty).mono (hpiece k hk)
  · intro k hk t ht
    exact (extChartAt I (z k)).map_source (by rw [extChartAt_source]; exact hP.1 k hk t ht)
  · intro k hk t ht
    have htroom : t ∈ Ioo (A k) (B k) := hpiece k hk ⟨ht.1.le, ht.2.le⟩
    have htV : t ∈ V := hroomV k hk htroom
    have hsrc : γ t ∈ (chartAt H (z k)).source := hroomsrc k hk t htroom
    exact (hasDerivAt_chartODE_of_isGeodesic (cov := cov) (x₀ := z k) hV htV hγ hsrc
      hgeov hnev).1
  · exact hγ.continuousOn.mono hVsub
  · intro t ht
    exact (hγ.contMDiffAt (hV.mem_nhds (hVsub ht))).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)



/-- **The `ParallelGlobal.GeodesicCover` of a chart-covered geodesic, with *prescribed* partition
and charts.**  This is Roadmap §117.2 step 3: with `(N, c, x) = (P.N, P.t, z)` the fields are the
room (`exists_room_of_isChartLoop`), the source condition on the room (same) and the geodesic
equation (`hasDerivAt_chartODE_of_isGeodesic`, evaluated at each time of the room — a germ condition,
so no covering argument is needed).  It opens the whole `Submission.ParallelGlobal` API (parallel
transport, `parallelField`, `transport_velocity`, `transport_norm`, …) to a curve given only as an
`IsChartLoop`. -/
theorem exists_geodesicCover_of_isChartLoop {P : Partition 0 1} {z : ℕ → M} {γ : ℝ → M}
    (hP : IsChartLoop (H := H) P γ z) (hγc : Continuous γ) {V : Set ℝ} (hV : IsOpen V)
    (hVsub : Icc (P.t 0) (P.t P.N) ⊆ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeov : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hnev : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0) :
    Nonempty (Submission.ParallelGlobal.GeodesicCover (I := I) cov γ (P.t 0) (P.t P.N)) := by
  obtain ⟨A, B, hAB, hroomV, hroomsrc⟩ := exists_room_of_isChartLoop hP hγc hV hVsub
  refine ⟨{ N := P.N, c := P.t, x := z, A := A, B := B, c_zero := rfl, c_last := rfl, mono := P.mono, room := ?_, src := ?_, ode := ?_ }⟩
  · exact hAB
  · exact fun k hk t ht => hroomsrc k hk t ht
  · intro k hk t ht
    exact hasDerivAt_chartODE_of_isGeodesic (cov := cov) (x₀ := z k) hV
      (hroomV k hk ht) hγ (hroomsrc k hk t ht) hgeov hnev


/-- **The `ParallelGlobal` piece solution and the `FundSol` fundamental solution agree.**  Both solve
the linear ODE `y' = -Γ̂(t)y` on `Icc (C.c k) (C.c (k+1))` with datum `v` at the left endpoint, so
they are equal by uniqueness (`ParallelGlobal.pieceSol_unique` applied to
`FundSol.fundSol_vector_hasDerivAt`).  This is the analytic core of the identification of
`ParallelGlobal.transport` with `Submission.HolDet.holAux` (Roadmap §122.6). -/
theorem pieceSol_eq_fundSolOn {a b : ℝ} (C : Submission.ParallelGlobal.GeodesicCover (I := I) cov γ a b)
    {k : ℕ} (hk : k < C.N) (htor : cov.torsion = 0) (v : E) :
    EqOn (fun t : ℝ => Submission.ParallelGlobal.pieceSol (cov := cov) htor C k v t)
      (fun t : ℝ => Submission.FundSol.fundSol (cov := cov) (x₀ := C.x k) htor (C.mono k hk)
        (Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
        (Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
        (Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk) t v)
      (Icc (C.c k) (C.c (k + 1))) := by
  refine (Submission.ParallelGlobal.pieceSol_unique (cov := cov) (htor := htor) (C := C)
    (k := k) (hk := hk) (v := v)
    (z := fun t : ℝ => Submission.FundSol.fundSol (cov := cov) (x₀ := C.x k) htor (C.mono k hk)
      (Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
      (Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
      (Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk) t v) ?_ ?_).symm
  · have h := congrArg (fun (L : E →L[ℝ] E) => L v)
      (Submission.FundSol.fundSol_datum (cov := cov) htor (C.mono k hk)
        (Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
        (Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
        (Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk))
    simpa using h
  · intro t ht
    exact Submission.FundSol.fundSol_vector_hasDerivAt (cov := cov) htor (C.mono k hk)
      (Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
      (Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
      (Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk) v t ht


/-- **The junction datum of `ParallelGlobal` is the chart transition of the piece solution.** -/
theorem nextDatum_eq_chartTransition {a b : ℝ} (C : Submission.ParallelGlobal.GeodesicCover (I := I) cov γ a b)
    {k : ℕ} (hk : k < C.N) (htor : cov.torsion = 0) (v : E)
    (hsrc' : γ (C.c (k + 1)) ∈ (chartAt H (C.x (k + 1))).source) :
    Submission.ParallelGlobal.nextDatum (cov := cov) htor C k v
      = chartTransition (I := I) (C.x k) (C.x (k + 1)) (γ (C.c (k + 1)))
          (Submission.ParallelGlobal.pieceSol (cov := cov) htor C k v (C.c (k + 1))) := by
  have hA1 : C.A k < C.c (k + 1) := lt_trans (C.room k hk).1 (C.mono k hk)
  have hB1 : C.c (k + 1) < C.B k := (C.room k hk).2
  have hx : γ (C.c (k + 1)) ∈ (chartAt H (C.x k)).source ∩ (chartAt H (C.x (k + 1))).source :=
    ⟨C.src k hk _ ⟨hA1, hB1⟩, hsrc'⟩
  have h1 : Submission.ParallelGlobal.nextDatum (cov := cov) htor C k v
      = (trivializationAt E (TangentSpace I) (C.x (k + 1))).continuousLinearMapAt ℝ
          (γ (C.c (k + 1)))
          (frameVector (I := I) (C.x k) (γ (C.c (k + 1)))
            (Submission.ParallelGlobal.pieceSol (cov := cov) htor C k v (C.c (k + 1)))) := rfl
  rw [h1, ← Submission.HolDet.chartTransition_frameVector (I := I) (z := C.x k) (z' := C.x (k + 1)) hx,
    Submission.GExpFlow.clm_frameVector (I := I) (by rw [extChartAt_source]; exact hsrc') _]


/-- **THE SYNGE INPUT FROM INTRINSIC GEOMETRY.**  Let `γ` be a closed chart-covered curve
(`IsChartLoop P γ z`, `γ (P.t P.N) = γ (P.t 0)`) with a periodic nonzero chart velocity, whose loop
sign is `1`, and which is a `C^∞` intrinsic geodesic on an open set `V` containing
`[P.t 0, P.t P.N]`.  If `Module.finrank ℝ E` is even, then there is `v ≠ 0` in the coordinates of the
chart `z 0`, orthogonal to the coordinate velocity, and fixed by the composite holonomy `holAux`
(for any admissible chart data `hu`, `hw`, `htgt` — the statement is independent of them by proof
irrelevance). -/
theorem exists_fixed_normal_coord_of_isChartLoop {P : Partition 0 1} {z : ℕ → M} {γ : ℝ → M}
    (hP : IsChartLoop (H := H) P γ z) (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hγc : Continuous γ) {V : Set ℝ} (hV : IsOpen V) (hVsub : Icc (P.t 0) (P.t P.N) ⊆ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeov : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hnev : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0)
    (hloop : γ (P.t P.N) = γ (P.t 0))
    (hvelper : deriv (coordC (I := I) (z := z) (γ := γ) P.N) (P.t P.N)
      = deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0))
    (hloopSign : loopSignOf (I := I) P γ z = 1)
    (hvelne : deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0) ≠ 0)
    (hEven : Even (Module.finrank ℝ E)) :
    ∃ v : E, v ≠ 0
      ∧ chartGram (I := I) (z 0) (γ (P.t 0))
          (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0)) v = 0
      ∧ (∀ (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k)
              (Icc (P.t k) (P.t (k+1))))
          (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
              (Icc (P.t k) (P.t (k+1))))
          (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
              coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target),
          holAux (cov := cov) htor hu hw htgt P.N v = v) := by
  obtain ⟨hsrc, hu₀, hw₀, htgt₀, hdiff, hγcont, hγmd⟩ :=
    chartData_of_isChartLoop (cov := cov) hP hγc hV hVsub hγ hgeov hnev
  obtain ⟨v, hvne, hvorth, hvfix⟩ :=
    exists_fixed_normal_coord_of_isGeodesic (cov := cov) hP hmet htor hdiff hγcont hsrc
      hu₀ hw₀ htgt₀ hγmd hV hVsub hγ hgeov hnev hloop hvelper hloopSign hvelne hEven
  refine ⟨v, hvne, hvorth, fun hu hw htgt => ?_⟩
  rw [Subsingleton.elim hu hu₀, Subsingleton.elim hw hw₀, Subsingleton.elim htgt htgt₀]
  exact hvfix

end

end Submission.HolDet
