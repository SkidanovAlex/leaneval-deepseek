import Submission.Commons.Analysis.Calculus.integral_eq_sub_of_hasDerivAt_of_continuousOn_Icc
import Submission.ParallelGlobal

/-!
# The parallel field along a geodesic: smoothness and parallelism on the rooms

`Submission.ParallelGlobal` constructs the global parallel field along a geodesic as a *piecewise*
chart-level solution of `y' = -Γ̂ y`, one solution per piece of a finite chart cover.  The values of
`exists_parallelChart`'s solution are only controlled on the closed piece, which makes the field's
smoothness (and hence its covariant derivative, since `covAlong` is defined through the chart
coordinates) unavailable at the *junctions* of the cover.

This file solves that by *re-running the chart-level ODE on a symmetric room around each piece*:

* **`roomA`/`roomB`** — the ends of the symmetric room `(roomA k, roomB k) ⊇ [c k, c (k+1)]` of
  piece `k`, strictly inside the room `(A k, B k)` of `GeodesicCover`;
* **`contDiffOn_coordPair`** — the bootstrap: the coordinate pair `(coordCurve, deriv coordCurve)` of
  the geodesic solves the autonomous system `y' = chartSpray y`, hence is `C^∞` on every closed
  subinterval of a room;
* **`contMDiffOn_gamma_room`** — the geodesic itself is `C^∞` on a room (chart bootstrap);
* **`exists_parallelChartAt`** — the chart-level parallel equation with the datum at an *interior*
  time;
* **`pieceSolR`** — the room solution with datum at `c k`, satisfying the ODE on the whole closed
  room; **`contDiffOn_pieceSolR`** — it is `C^∞` on the closed room;
* **`pieceFieldR`** — the field along `γ` with those chart coordinates;
  **`smoothAlongAt_pieceFieldR`** — it is smooth along `γ` at every point of the open room;
* **`SmoothAlongAt_congr`** — `SmoothAlongAt` only depends on the germ of the field;
* **`covAlong_eq_zero_of_germ`** / **`covAlong_pieceFieldR`** — **the field is parallel along `γ`**:
  `covAlong cov (pieceFieldR …) t = 0`, proved by the chart independence of the parallel equation
  (`chartCovDeriv_eq_zero_iff`, `chartCovDeriv_eq_DtQ`, `covAlong_eq_chart`).

The remaining step for the *global* field (a piecewise assembly over `kOf`) is the **overlap
agreement** of adjacent piece fields on a neighbourhood of a junction, which is a uniqueness
statement for the parallel ODE (see `Submission/Roadmap.lean` §114).
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
open Submission.JacobiTensor
open Submission.Jacobi
open Submission.ParallelGlobal
open Submission.JacobiGlobal

namespace Submission.ParallelRoom

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
variable {γ : ℝ → M} {a b : ℝ}

/-- **The chart coordinate pair of a geodesic is `C^∞` on every closed subinterval of a room.**
This is the bootstrap for the geodesic equation, written as the first order system
`y' = chartSpray (x k) y` with `y = (coordCurve, deriv coordCurve)`. -/
theorem contDiffOn_coordPair (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N)
    {a' b' : ℝ} (ha' : C.A k < a') (hb' : b' < C.B k) (hab' : a' < b') :
    ContDiffOn ℝ ∞ (fun t => (coordCurve (I := I) C k t,
      deriv (coordCurve (I := I) C k) t)) (Icc a' b') := by
  have hsub : Icc a' b' ⊆ Set.Ioo (C.A k) (C.B k) := fun t ht =>
    ⟨lt_of_lt_of_le ha' ht.1, lt_of_le_of_lt ht.2 hb'⟩
  have hderiv : ∀ t ∈ Icc a' b', HasDerivAt
      (fun t => (coordCurve (I := I) C k t, deriv (coordCurve (I := I) C k) t))
      (Submission.GExpFlow.chartSpray (cov := cov) (C.x k)
        ((coordCurve (I := I) C k t, deriv (coordCurve (I := I) C k) t))) t := by
    intro t ht
    have h1 := (C.ode k hk t (hsub ht)).1
    have h2 := (C.ode k hk t (hsub ht)).2
    have h := h1.prodMk h2
    rw [Submission.GExpFlow.chartSpray_apply]
    exact h
  exact Commons.Analysis.ODE.contDiffOn_infty_of_hasDerivAt (F :=
      Submission.GExpFlow.chartSpray (cov := cov) (C.x k))
    (V := (extChartAt I (C.x k)).target ×ˢ (univ : Set E)) hab'
    (Submission.GExpFlow.contDiffOn_chartSpray (cov := cov) (C.x k))
    (fun t ht => ⟨(extChartAt I (C.x k)).map_source (by
        rw [extChartAt_source]; exact C.src k hk t (hsub ht)), trivial⟩)
    hderiv (HasDerivAt.continuousOn hderiv)


/-! ## §2 The room subintervals -/

/-- The left end of the *symmetric* room of piece `k`, inside `(A k, c k)`. -/
noncomputable def roomA (C : GeodesicCover cov γ a b) (k : ℕ) : ℝ := (C.A k + C.c k) / 2

/-- The right end of the *symmetric* room of piece `k`, inside `(c (k+1), B k)`. -/
noncomputable def roomB (C : GeodesicCover cov γ a b) (k : ℕ) : ℝ := (C.B k + C.c (k + 1)) / 2

theorem A_lt_roomA (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    C.A k < roomA C k := by
  rw [roomA]; linarith [(C.room k hk).1]

theorem roomA_lt_c (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    roomA C k < C.c k := by
  rw [roomA]; linarith [(C.room k hk).1]

theorem c_succ_lt_roomB (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    C.c (k + 1) < roomB C k := by
  rw [roomB]; linarith [(C.room k hk).2]

theorem roomB_lt_B (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    roomB C k < C.B k := by
  rw [roomB]; linarith [(C.room k hk).2]

theorem roomA_lt_roomB (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    roomA C k < roomB C k := by
  have h1 := roomA_lt_c C hk
  have h2 := (C.mono k hk)
  have h3 := c_succ_lt_roomB C hk
  linarith

theorem room_subset (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    Icc (roomA C k) (roomB C k) ⊆ Ioo (C.A k) (C.B k) := fun t ht =>
  ⟨lt_of_lt_of_le (A_lt_roomA C hk) ht.1, lt_of_le_of_lt ht.2 (roomB_lt_B C hk)⟩

/-! ## §3 Smoothness of the coordinate pair on the rooms -/

/-- The coordinate pair of the geodesic is `C^∞` at every point of a room. -/
theorem contDiffAt_coordPair_room (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N)
    {t : ℝ} (ht : t ∈ Ioo (C.A k) (C.B k)) :
    ContDiffAt ℝ ∞ (fun s => (coordCurve (I := I) C k s,
      deriv (coordCurve (I := I) C k) s)) t := by
  set a' : ℝ := (C.A k + t) / 2 with ha'def
  set b' : ℝ := (t + C.B k) / 2 with hb'def
  have ha' : C.A k < a' := by rw [ha'def]; linarith [ht.1]
  have hb' : b' < C.B k := by rw [hb'def]; linarith [ht.2]
  have hab' : a' < b' := by rw [ha'def, hb'def]; linarith [ht.1, ht.2]
  have htmem : t ∈ Ioo a' b' := by
    rw [ha'def, hb'def]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact (contDiffOn_coordPair (cov := cov) C hk ha' hb' hab').contDiffAt
    (Icc_mem_nhds htmem.1 htmem.2)

theorem contDiffOn_coordPair_room (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    ContDiffOn ℝ ∞ (fun s => (coordCurve (I := I) C k s,
      deriv (coordCurve (I := I) C k) s)) (Ioo (C.A k) (C.B k)) :=
  fun t ht => (contDiffAt_coordPair_room (cov := cov) C hk ht).contDiffWithinAt

theorem contDiffOn_coordCurve_room (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    ContDiffOn ℝ ∞ (coordCurve (I := I) C k) (Ioo (C.A k) (C.B k)) :=
  fun t ht => (contDiffAt_coordPair_room (cov := cov) C hk ht).fst.contDiffWithinAt

theorem contDiffOn_deriv_coordCurve_room (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    ContDiffOn ℝ ∞ (deriv (coordCurve (I := I) C k)) (Ioo (C.A k) (C.B k)) :=
  fun t ht => (contDiffAt_coordPair_room (cov := cov) C hk ht).snd.contDiffWithinAt

/-- The target-membership of the coordinate curve on a room. -/
theorem coordCurve_mem_target_room (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    ∀ t ∈ Ioo (C.A k) (C.B k), coordCurve (I := I) C k t ∈ (extChartAt I (C.x k)).target := by
  intro t ht
  exact (extChartAt I (C.x k)).map_source (by
    rw [extChartAt_source]; exact C.src k hk t ht)


/-- Continuity of the coordinate curve on the closed room. -/
theorem continuousOn_coordCurve_room_closed (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    ContinuousOn (coordCurve (I := I) C k) (Icc (roomA C k) (roomB C k)) := fun t ht =>
  ((contDiffAt_coordPair_room (cov := cov) C hk (room_subset C hk ht)).fst).continuousAt.continuousWithinAt

/-- Continuity of the chart velocity on the closed room. -/
theorem continuousOn_deriv_coordCurve_room_closed (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) :
    ContinuousOn (deriv (coordCurve (I := I) C k)) (Icc (roomA C k) (roomB C k)) := fun t ht =>
  ((contDiffAt_coordPair_room (cov := cov) C hk (room_subset C hk ht)).snd).continuousAt.continuousWithinAt

/-! ## §4 The chart-level parallel equation with datum at an interior time -/

/-- **The chart-level parallel equation** `y' = -Γ̂ y` on `[a,b]` with datum at an arbitrary time
`t₀ ∈ Icc a b`.  (Only the values on `[a,b]` are controlled.) -/
theorem exists_parallelChartAt (htor : cov.torsion = 0)
    {x₀ : M} {u w : ℝ → E} {a b t₀ : ℝ} (hab : a < b)
    (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) (ht₀ : t₀ ∈ Icc a b) (y₀ : E) :
    ∃ y : ℝ → E, y t₀ = y₀ ∧ (∀ t ∈ Icc a b,
        HasDerivAt y (-(gammaOp (cov := cov) x₀ u w t (y t))) t) ∧
      ∀ z : ℝ → E, z t₀ = y₀ →
        (∀ t ∈ Icc a b, HasDerivAt z (-(gammaOp (cov := cov) x₀ u w t (z t))) t) →
        EqOn z y (Icc a b) := by
  have hA : ContinuousOn (fun t : ℝ => -(gammaOp (cov := cov) x₀ u w t)) (Icc a b) :=
    (Submission.IndexCorner2.continuousOn_gammaOp_of_cont (cov := cov) htor hu hw htgt).neg
  obtain ⟨y, hy0, hyd, hyu⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc (E := E) hab hA ht₀ y₀
  exact ⟨y, hy0, hyd, fun z hz0 hz => hyu z hz0 hz⟩

/-! ## §5 The room solution of the parallel equation -/

/-- **The parallel solution on the room of piece `k`**, with datum `v` at `c k`.  This is the
version of `ParallelGlobal.pieceSol` whose values are controlled on a *neighbourhood* of the closed
piece (`Icc (roomA k) (roomB k) ⊇ [c k, c (k+1)]`). -/
noncomputable def pieceSolR (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) (k : ℕ) (v : E) :
    ℝ → E :=
  if hk : k < C.N then
    Classical.choose (exists_parallelChartAt (cov := cov) htor (roomA_lt_roomB C hk)
      (continuousOn_coordCurve_room_closed (cov := cov) C hk)
      (continuousOn_deriv_coordCurve_room_closed (cov := cov) C hk)
      (fun t ht => coordCurve_mem_target_room (cov := cov) C hk t (room_subset C hk ht))
      ⟨(roomA_lt_c C hk).le, (C.mono k hk).le.trans (c_succ_lt_roomB C hk).le⟩ v)
  else fun _ => 0

theorem pieceSolR_eq_choose (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) :
    pieceSolR (cov := cov) htor C k v = Classical.choose
      (exists_parallelChartAt (cov := cov) htor (roomA_lt_roomB C hk)
      (continuousOn_coordCurve_room_closed (cov := cov) C hk)
      (continuousOn_deriv_coordCurve_room_closed (cov := cov) C hk)
      (fun t ht => coordCurve_mem_target_room (cov := cov) C hk t (room_subset C hk ht))
      ⟨(roomA_lt_c C hk).le, (C.mono k hk).le.trans (c_succ_lt_roomB C hk).le⟩ v) := by
  rw [pieceSolR, dif_pos hk]

theorem pieceSolR_datum (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) : pieceSolR (cov := cov) htor C k v (C.c k) = v := by
  rw [pieceSolR_eq_choose (cov := cov) htor C hk v]
  exact (Classical.choose_spec (exists_parallelChartAt (cov := cov) htor (roomA_lt_roomB C hk)
      (continuousOn_coordCurve_room_closed (cov := cov) C hk)
      (continuousOn_deriv_coordCurve_room_closed (cov := cov) C hk)
      (fun t ht => coordCurve_mem_target_room (cov := cov) C hk t (room_subset C hk ht))
      ⟨(roomA_lt_c C hk).le, (C.mono k hk).le.trans (c_succ_lt_roomB C hk).le⟩ v)).1

theorem pieceSolR_ode (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) :
    ∀ t ∈ Icc (roomA C k) (roomB C k), HasDerivAt (pieceSolR (cov := cov) htor C k v)
      (-(gammaOp (cov := cov) (C.x k) (coordCurve (I := I) C k)
        (deriv (coordCurve (I := I) C k)) t (pieceSolR (cov := cov) htor C k v t))) t := by
  rw [pieceSolR_eq_choose (cov := cov) htor C hk v]
  exact (Classical.choose_spec (exists_parallelChartAt (cov := cov) htor (roomA_lt_roomB C hk)
      (continuousOn_coordCurve_room_closed (cov := cov) C hk)
      (continuousOn_deriv_coordCurve_room_closed (cov := cov) C hk)
      (fun t ht => coordCurve_mem_target_room (cov := cov) C hk t (room_subset C hk ht))
      ⟨(roomA_lt_c C hk).le, (C.mono k hk).le.trans (c_succ_lt_roomB C hk).le⟩ v)).2.1

/-- The room solution satisfies the same equation on the *closed piece*. -/
theorem pieceSolR_ode_piece (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) :
    ∀ t ∈ Icc (C.c k) (C.c (k + 1)), HasDerivAt (pieceSolR (cov := cov) htor C k v)
      (-(gammaOp (cov := cov) (C.x k) (coordCurve (I := I) C k)
        (deriv (coordCurve (I := I) C k)) t (pieceSolR (cov := cov) htor C k v t))) t := by
  refine fun t ht => pieceSolR_ode (cov := cov) htor C hk v t ?_
  exact ⟨(roomA_lt_c C hk).le.trans ht.1, ht.2.trans (c_succ_lt_roomB C hk).le⟩

/-- **Smoothness of the room solution on the room** (the geometric payoff: the chart coordinates of
the parallel field are `C^∞` on a neighbourhood of the closed piece). -/
theorem contDiffOn_pieceSolR (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) :
    ContDiffOn ℝ ∞ (pieceSolR (cov := cov) htor C k v) (Icc (roomA C k) (roomB C k)) := by
  set G : ℝ → E → E := fun t p => -(gammaOp (cov := cov) (C.x k) (coordCurve (I := I) C k)
    (deriv (coordCurve (I := I) C k)) t) p with hGdef
  have hG : ContDiffOn ℝ ∞ (fun p : ℝ × E => G p.1 p.2)
      (Ioo (C.A k) (C.B k) ×ˢ (univ : Set E)) := by
    have hbase : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
        -(gammaOp (cov := cov) (C.x k) (coordCurve (I := I) C k)
          (deriv (coordCurve (I := I) C k)) p.1)) (Ioo (C.A k) (C.B k) ×ˢ (univ : Set E)) := by
      refine ((Submission.Coeff.contDiffOn_gammaOp_along_Ioo (cov := cov) htor
        (fun t ht => coordCurve_mem_target_room (cov := cov) C hk t ht)
        (contDiffOn_coordCurve_room (cov := cov) C hk)
        (contDiffOn_deriv_coordCurve_room (cov := cov) C hk)).neg).comp contDiffOn_fst ?_
      intro p hp
      exact hp.1
    exact hbase.clm_apply contDiffOn_snd
  have hode : ∀ t ∈ uIcc (roomA C k) (roomB C k),
      HasDerivAt (pieceSolR (cov := cov) htor C k v) (G t (pieceSolR (cov := cov) htor C k v t)) t := by
    intro t ht
    rw [uIcc_of_le (roomA_lt_roomB C hk).le] at ht
    exact pieceSolR_ode (cov := cov) htor C hk v t ht
  have hyU : ∀ t ∈ uIcc (roomA C k) (roomB C k),
      (t, pieceSolR (cov := cov) htor C k v t) ∈ (Ioo (C.A k) (C.B k) ×ˢ (univ : Set E)) := by
    intro t ht
    rw [uIcc_of_le (roomA_lt_roomB C hk).le] at ht
    exact ⟨room_subset C hk ht, trivial⟩
  have hyc : ContinuousOn (pieceSolR (cov := cov) htor C k v)
      (uIcc (roomA C k) (roomB C k)) :=
    HasDerivAt.continuousOn hode
  refine contDiffOn_infty.mpr (fun n => ?_)
  refine (Commons.Analysis.ODE.contDiffOn_of_hasDerivAt_of_contDiffOn (n := n) (G := G)
    (hG.of_le ?_) hyU hode hyc).mono ?_
  · show ((n : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  · rw [uIcc_of_le (roomA_lt_roomB C hk).le]


/-! ## §6 The field of the room solution, its smoothness and its parallelism -/

/-- `γ` is `C^∞` on the room (from the chart ODE bootstrap). -/
theorem contMDiffOn_gamma_room (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (C.A k) (C.B k)) := by
  have hcomp : ContMDiffOn 𝓘(ℝ) I ∞
      (fun t => (extChartAt I (C.x k)).symm (coordCurve (I := I) C k t))
      (Ioo (C.A k) (C.B k)) :=
    (contMDiffOn_extChartAt_symm (I := I) (C.x k)).comp
      ((contDiffOn_coordCurve_room (cov := cov) C hk).contMDiffOn)
      (fun t ht => coordCurve_mem_target_room (cov := cov) C hk t ht)
  refine hcomp.congr (fun t ht => ?_)
  exact (PartialEquiv.left_inv (extChartAt I (C.x k)) (by
    rw [extChartAt_source]; exact C.src k hk t ht)).symm

/-- The field along `γ` whose chart-`x k` coordinates are the room solution. -/
noncomputable def pieceFieldR (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) (k : ℕ) (v : E) :
    (t : ℝ) → TangentSpace I (γ t) :=
  fun t => frameVector (I := I) (C.x k) (γ t) (pieceSolR (cov := cov) htor C k v t)

theorem pieceFieldR_apply (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) (k : ℕ) (v : E)
    (t : ℝ) :
    pieceFieldR (cov := cov) htor C k v t
      = frameVector (I := I) (C.x k) (γ t) (pieceSolR (cov := cov) htor C k v t) := rfl

/-- **The field of the room solution is smooth along `γ`** on the closed room. -/
theorem smoothAlongAt_pieceFieldR (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) {t : ℝ} (ht : t ∈ Ioo (roomA C k) (roomB C k)) :
    SmoothAlongAt (I := I) γ (pieceFieldR (cov := cov) htor C k v) t := by
  -- `γ` is continuous at `t`, hence stays in its own chart near `t`
  have hcontAt : ContinuousAt γ t :=
    ((contMDiffOn_gamma_room (cov := cov) C hk).contMDiffAt
      ((isOpen_Ioo).mem_nhds (room_subset C hk ⟨ht.1.le, ht.2.le⟩))).continuousAt
  have hev : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (γ t)).source :=
    Submission.JacobiGlobal.eventually_mem_source_self (H := H) hcontAt
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hev
  set U : Set ℝ := Ioo (max (roomA C k) (t - ε)) (min (roomB C k) (t + ε)) with hUdef
  have hUopen : IsOpen U := by rw [hUdef]; exact isOpen_Ioo
  have htU : t ∈ U := by
    rw [hUdef]
    exact ⟨max_lt ht.1 (by linarith), lt_min ht.2 (by linarith)⟩
  have hUsub : U ⊆ Ioo (C.A k) (C.B k) := by
    intro s hs
    refine room_subset C hk ⟨?_, ?_⟩
    · rw [hUdef] at hs
      exact le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs.1)
    · rw [hUdef] at hs
      exact le_of_lt (lt_of_lt_of_le hs.2 (min_le_left _ _))
  have hUsub' : U ⊆ Ioo (roomA C k) (roomB C k) := fun s hs => by
    rw [hUdef] at hs
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  have hUsub'' : U ⊆ Icc (roomA C k) (roomB C k) := fun s hs => by
    rw [hUdef] at hs
    exact ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs.1),
      le_of_lt (lt_of_lt_of_le hs.2 (min_le_left _ _))⟩
  have hUball : U ⊆ Metric.ball t ε := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq]
    rw [hUdef] at hs
    rw [abs_lt]
    exact ⟨by linarith [lt_of_le_of_lt (le_max_right (roomA C k) (t - ε)) hs.1],
           by linarith [lt_of_lt_of_le hs.2 (min_le_right (roomB C k) (t + ε))]⟩
  refine Submission.JacobiGlobal.smoothAlongAt_frameVector (I := I)
    (z := C.x k) (a := pieceSolR (cov := cov) htor C k v) (γ := γ) (U := U) (t := t)
    hUopen htU ?_ ?_ ?_ ?_
  · exact (contDiffOn_pieceSolR (cov := cov) htor C hk v).mono hUsub''
  · exact (contMDiffOn_gamma_room (cov := cov) C hk).mono hUsub
  · intro s hs
    exact C.src k hk s (hUsub hs)
  · intro s hs
    exact hεsub (hUball hs)


/-- **`SmoothAlongAt` only depends on the germ of the field.** -/
theorem SmoothAlongAt_congr {V W : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hV : SmoothAlongAt (I := I) γ V t) (h : V =ᶠ[𝓝 t] W) :
    SmoothAlongAt (I := I) γ W t := by
  obtain ⟨U, hUopen, htU, hsrc, hcd⟩ := hV
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp h
  set U' : Set ℝ := U ∩ Ioo (t - ε) (t + ε) with hU'def
  have hU'open : IsOpen U' := hUopen.inter isOpen_Ioo
  have htU' : t ∈ U' := ⟨htU, ⟨by linarith, by linarith⟩⟩
  refine ⟨U', hU'open, htU', fun s hs => hsrc s hs.1, ?_⟩
  refine ContDiffOn.congr (f := Submission.JacobiCoords.chartCoords (I := I) (γ t) γ V) ?_ (fun s hs => ?_)
  · exact hcd.mono (fun s hs => hs.1)
  · have hsball : s ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩
    simp only [Submission.JacobiCoords.chartCoords]
    rw [(hεsub hsball).symm]

/-- **A field that agrees near `t` with the piece-`k` field is parallel at `t`.**  The chart
independence of the parallel equation: in the chart of the piece the equation `y' = -Γ̂ y` holds by
`pieceSolR_ode`, and `chartCovDeriv_eq_zero_iff` + `chartCovDeriv_eq_DtQ` convert it into the
vanishing of `covAlong`. -/
theorem covAlong_eq_zero_of_germ (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) {t : ℝ} (ht : t ∈ Ioo (roomA C k) (roomB C k))
    (hγt : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : curveVelocity (I := I) γ t ≠ 0)
    {V : (t : ℝ) → TangentSpace I (γ t)} (hV : SmoothAlongAt (I := I) γ V t)
    (hgerm : V =ᶠ[𝓝 t] pieceFieldR (cov := cov) htor C k v) :
    covAlong cov V t = 0 := by
  have htIcc : t ∈ Icc (roomA C k) (roomB C k) := ⟨ht.1.le, ht.2.le⟩
  have htroom : t ∈ Ioo (C.A k) (C.B k) := room_subset C hk htIcc
  have hRn : Ioo (roomA C k) (roomB C k) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have hAn : Ioo (C.A k) (C.B k) ∈ 𝓝 t := isOpen_Ioo.mem_nhds htroom
  have hsrc : γ t ∈ (chartAt H (C.x k)).source := C.src k hk t htroom
  have hsrcEv : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (C.x k)).source := by
    filter_upwards [hAn] with s hs
    exact C.src k hk s hs
  have huTgt : ∀ᶠ s in 𝓝 t, coordCurve (I := I) C k s ∈ (extChartAt I (C.x k)).target := by
    filter_upwards [hsrcEv] with s hs
    exact (extChartAt I (C.x k)).map_source (by rwa [extChartAt_source])
  have hγeq : γ =ᶠ[𝓝 t] fun s => (extChartAt I (C.x k)).symm (coordCurve (I := I) C k s) := by
    filter_upwards [hsrcEv] with s hs
    exact (PartialEquiv.left_inv (extChartAt I (C.x k)) (by rwa [extChartAt_source])).symm
  have hu : ∀ᶠ s in 𝓝 t, HasDerivAt (coordCurve (I := I) C k)
      (deriv (coordCurve (I := I) C k) s) s := by
    filter_upwards [hAn] with s hs
    exact (C.ode k hk s hs).1
  have hy : ∀ᶠ s in 𝓝 t, frameVector (I := I) (C.x k) (γ s)
      (pieceSolR (cov := cov) htor C k v s) = V s := by
    filter_upwards [hgerm] with s hs
    rw [hs]
    rfl
  have hy' : ∀ᶠ s in 𝓝 t, HasDerivAt (pieceSolR (cov := cov) htor C k v)
      (deriv (pieceSolR (cov := cov) htor C k v) s) s := by
    filter_upwards [hRn] with s hs
    have h := pieceSolR_ode (cov := cov) htor C hk v s ⟨hs.1.le, hs.2.le⟩
    exact h.congr_deriv h.deriv.symm
  have hchart := Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor hγt hne hV hsrc
    hsrcEv huTgt hγeq hu hy hy'
  rw [hchart]
  have hsymm : (extChartAt I (C.x k)).symm (coordCurve (I := I) C k t) ∈
      (chartAt H (C.x k)).source := by
    have h1 : (extChartAt I (C.x k)).symm ((extChartAt I (C.x k)) (γ t)) ∈
        (chartAt H (C.x k)).source := by
      rw [PartialEquiv.left_inv (extChartAt I (C.x k)) (by
        rw [extChartAt_source]; exact C.src k hk t htroom)]
      exact hsrc
    exact h1
  have hzero : Submission.Jacobi.chartCovDeriv cov (C.x k) (coordCurve (I := I) C k)
      (deriv (coordCurve (I := I) C k)) (pieceSolR (cov := cov) htor C k v) t = 0 :=
    Submission.ParallelField.chartCovDeriv_eq_zero_iff (cov := cov)
      (huTgt.self_of_nhds)
      (pieceSolR_ode (cov := cov) htor C hk v t htIcc)
  have hDtQ : Submission.BonnetMyers.DtQ cov (C.x k) (coordCurve (I := I) C k)
      (pieceSolR (cov := cov) htor C k v) (deriv (coordCurve (I := I) C k))
      (deriv (pieceSolR (cov := cov) htor C k v)) t = 0 := by
    rw [← Submission.IndexCorner.chartCovDeriv_eq_DtQ (cov := cov) htor (C.x k)
      (u := coordCurve (I := I) C k) (w := deriv (coordCurve (I := I) C k))
      (F := pieceSolR (cov := cov) htor C k v) (F' := deriv (pieceSolR (cov := cov) htor C k v))
      hsymm (hy'.self_of_nhds), hzero]
  rw [hDtQ, Submission.ChartBounds.frameVector_zero']

/-- **The field of the room solution is parallel along `γ`.** -/
theorem covAlong_pieceFieldR (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) {t : ℝ} (ht : t ∈ Ioo (roomA C k) (roomB C k))
    (hγt : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : curveVelocity (I := I) γ t ≠ 0) :
    covAlong cov (pieceFieldR (cov := cov) htor C k v) t = 0 :=
  covAlong_eq_zero_of_germ (cov := cov) htor C hk v ht hγt hne
    (smoothAlongAt_pieceFieldR (cov := cov) htor C hk v ht)
    (Filter.EventuallyEq.refl _ _)

/-- **Two parallel fields along a curve have constant inner product.**  This is metric
compatibility: `d/dt ⟪U,W⟫ = ⟪∇U,W⟫ + ⟪U,∇W⟫ = 0`. -/
theorem isConst_inner_of_parallel (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {U W : (t : ℝ) → TangentSpace I (γ t)} {α β : ℝ} (hαβ : α < β) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo α β)
    (hγ1 : ∀ t ∈ Ioo α β, ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ t ∈ Ioo α β, curveVelocity (I := I) γ t ≠ 0)
    (hU : ∀ t ∈ Ioo α β, SmoothAlongAt (I := I) γ U t)
    (hW : ∀ t ∈ Ioo α β, SmoothAlongAt (I := I) γ W t)
    (hUp : ∀ t ∈ Ioo α β, covAlong cov U t = 0)
    (hWp : ∀ t ∈ Ioo α β, covAlong cov W t = 0) :
    ∀ t ∈ Ioo α β, inner ℝ (U t) (W t) = inner ℝ (U t₀) (W t₀) := by
  have hderiv : ∀ t ∈ Ioo α β, HasDerivAt (fun s => inner ℝ (U s) (W s)) 0 t := by
    intro t ht
    obtain ⟨𝒱, h𝒱sm, h𝒱ev⟩ :=
      exists_section_of_smoothAlongAt (hγ1 t ht) (hne t ht) (hU t ht)
    obtain ⟨𝒲, h𝒲sm, h𝒲ev⟩ :=
      exists_section_of_smoothAlongAt (hγ1 t ht) (hne t ht) (hW t ht)
    have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t :=
      ((hγ1 t ht).contMDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).mdifferentiableAt (by simp)
    have h1 := Submission.Variation.hasDerivAt_inner_sections cov hmet h𝒱sm h𝒲sm hγmd
    have hev : (fun s => inner ℝ (𝒱 (γ s)) (𝒲 (γ s))) =ᶠ[𝓝 t]
        (fun s => inner ℝ (U s) (W s)) := by
      filter_upwards [h𝒱ev, h𝒲ev] with s h1 h2
      rw [h1, h2]
    refine (h1.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    rw [← covAlong_eq_cov (cov := cov) htor (hγ1 t ht) (hne t ht) (hU t ht) h𝒱sm h𝒱ev,
        ← covAlong_eq_cov (cov := cov) htor (hγ1 t ht) (hne t ht) (hW t ht) h𝒲sm h𝒲ev,
        hUp t ht, hWp t ht, inner_zero_left, inner_zero_right, add_zero]
  intro t ht
  rcases lt_trichotomy t t₀ with h | h | h
  · have hsub : Icc t t₀ ⊆ Ioo α β := fun s hs =>
      ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 ht₀.2⟩
    have hcont : ContinuousOn (fun s => inner ℝ (U s) (W s)) (Icc t t₀) :=
      HasDerivAt.continuousOn (fun s hs => hderiv s (hsub hs))
    have hder : ∀ s ∈ Ioo t t₀, HasDerivAt (fun s => inner ℝ (U s) (W s))
        ((fun _ : ℝ => (0 : ℝ)) s) s := fun s hs => hderiv s (hsub (Ioo_subset_Icc_self hs))
    have hkey := Commons.Analysis.Calculus.integral_eq_sub_of_hasDerivAt_of_continuousOn_Icc
      (F := fun s => inner ℝ (U s) (W s)) (g := fun _ : ℝ => (0 : ℝ)) h.le hcont
      continuousOn_const hder
    rw [intervalIntegral.integral_zero] at hkey
    linarith
  · rw [h]
  · have hsub : Icc t₀ t ⊆ Ioo α β := fun s hs =>
      ⟨lt_of_lt_of_le ht₀.1 hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hcont : ContinuousOn (fun s => inner ℝ (U s) (W s)) (Icc t₀ t) :=
      HasDerivAt.continuousOn (fun s hs => hderiv s (hsub hs))
    have hder : ∀ s ∈ Ioo t₀ t, HasDerivAt (fun s => inner ℝ (U s) (W s))
        ((fun _ : ℝ => (0 : ℝ)) s) s := fun s hs => hderiv s (hsub (Ioo_subset_Icc_self hs))
    have hkey := Commons.Analysis.Calculus.integral_eq_sub_of_hasDerivAt_of_continuousOn_Icc
      (F := fun s => inner ℝ (U s) (W s)) (g := fun _ : ℝ => (0 : ℝ)) h.le hcont
      continuousOn_const hder
    rw [intervalIntegral.integral_zero] at hkey
    linarith

/-- **Uniqueness of the parallel field along a curve**: two parallel fields agreeing at one point
agree on the whole interval.  Proof: the three pairings `⟨U,U⟩`, `⟨U,W⟩`, `⟨W,W⟩` are constant
(`isConst_inner_of_parallel`), so `‖U - W‖²` is constant, and it vanishes at the base point. -/
theorem eqOn_of_parallel (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {U W : (t : ℝ) → TangentSpace I (γ t)} {α β : ℝ} (hαβ : α < β) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo α β)
    (hγ1 : ∀ t ∈ Ioo α β, ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ t ∈ Ioo α β, curveVelocity (I := I) γ t ≠ 0)
    (hU : ∀ t ∈ Ioo α β, SmoothAlongAt (I := I) γ U t)
    (hW : ∀ t ∈ Ioo α β, SmoothAlongAt (I := I) γ W t)
    (hUp : ∀ t ∈ Ioo α β, covAlong cov U t = 0)
    (hWp : ∀ t ∈ Ioo α β, covAlong cov W t = 0)
    (heq : U t₀ = W t₀) :
    ∀ t ∈ Ioo α β, U t = W t := by
  have hUU := isConst_inner_of_parallel (cov := cov) hmet htor hαβ ht₀ hγ1 hne hU hU hUp hUp
  have hUW := isConst_inner_of_parallel (cov := cov) hmet htor hαβ ht₀ hγ1 hne hU hW hUp hWp
  have hWW := isConst_inner_of_parallel (cov := cov) hmet htor hαβ ht₀ hγ1 hne hW hW hWp hWp
  intro t ht
  have h0 : inner ℝ (U t - W t) (U t - W t) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    rw [← real_inner_comm (W t) (U t)]
    rw [hUU t ht, hUW t ht, hWW t ht, heq]
    ring
  have hnorm : ‖U t - W t‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq]; exact h0
  exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp hnorm))


/-! ## §9 The global field assembled over the cover -/

/-- The datum of the next piece (the chart-`x (k+1)` coordinates of the piece-`k` field at the
junction). -/
noncomputable def nextDatumR (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) (k : ℕ) (v : E) :
    E :=
  Submission.JacobiCoords.chartCoords (I := I) (C.x (k + 1)) γ
    (pieceFieldR (cov := cov) htor C k v) (C.c (k + 1))

/-- The datum of every piece. -/
noncomputable def datumAtR (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) (v₀ : E) :
    ℕ → E :=
  Nat.rec v₀ (fun k v => nextDatumR (cov := cov) htor C k v)

theorem datumAtR_zero (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) (v₀ : E) :
    datumAtR (cov := cov) htor C v₀ 0 = v₀ := rfl

/-- **The global parallel field along `γ`**, built from the room solutions. -/
noncomputable def parallelFieldR (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b)
    (hN : 0 < C.N) (v₀ : E) : (t : ℝ) → TangentSpace I (γ t) :=
  fun t => pieceFieldR (cov := cov) htor C (kOf (cov := cov) C hN t)
    (datumAtR (cov := cov) htor C v₀ (kOf (cov := cov) C hN t)) t

/-- `kOf` never reaches the last index. -/
theorem kOf_lt_N (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (t : ℝ) :
    kOf (cov := cov) C hN t < C.N := by
  have h := kOf_le (cov := cov) C hN t
  omega

/-- For `t > a` the index `kOf` is *strictly* to the left of `t`. -/
theorem c_kOf_lt_of_lt (C : GeodesicCover cov γ a b) (hN : 0 < C.N) {t : ℝ} (ha : C.c 0 < t) :
    C.c (kOf (cov := cov) C hN t) < t := by
  by_contra hcon
  rw [not_lt] at hcon
  have hk : kOf (cov := cov) C hN t ≠ 0 := by
    intro h0
    rw [h0, C.c_zero] at hcon
    rw [C.c_zero] at ha
    linarith
  obtain ⟨m, hm⟩ : ∃ m, kOf (cov := cov) C hN t = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hk)).symm⟩
  have hmin := kOf_min (cov := cov) C hN t (k := m) (by rw [hm]; exact Nat.lt_succ_self m)
  exact hmin (le_trans (min_le_left _ _) (by rw [hm] at hcon; exact hcon))

/-- The germ of `parallelFieldR` in the *interior* of a piece is the piece field of that piece. -/
theorem parallelFieldR_eventuallyEq_piece (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b)
    (hN : 0 < C.N) (v₀ : E) {k : ℕ} (hk : k < C.N) {t : ℝ} (hlo : C.c k < t)
    (hhi : t < C.c (k + 1)) :
    parallelFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C hN v₀ =ᶠ[𝓝 t]
      pieceFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C k
        (datumAtR (cov := cov) htor C v₀ k) := by
  refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show t ∈ Ioo (C.c k) (C.c (k + 1)) from
    ⟨hlo, hhi⟩)) (fun s hs => ?_)
  show pieceFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C
      (kOf (cov := cov) C hN s) (datumAtR (cov := cov) htor C v₀ (kOf (cov := cov) C hN s)) s = _
  rw [kOf_eq_of_mem (cov := cov) C hN hk hs.1 hs.2.le]

/-- The germ of `parallelFieldR` at `C.c 0` is the *first* piece field. -/
theorem parallelFieldR_eventuallyEq_piece_zero (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b)
    (hN : 0 < C.N) (v₀ : E) :
    parallelFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C hN v₀ =ᶠ[𝓝 (C.c 0)]
      pieceFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C 0 v₀ := by
  refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show C.c 0 ∈ Ioo (roomA C 0) (C.c 1) from
    ⟨roomA_lt_c (cov := cov) C (k := 0) hN, C.mono 0 hN⟩)) (fun s hs => ?_)
  show pieceFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C
      (kOf (cov := cov) C hN s) (datumAtR (cov := cov) htor C v₀ (kOf (cov := cov) C hN s)) s
    = pieceFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C 0 v₀ s
  have hk0 : kOf (cov := cov) C hN s = 0 :=
    Nat.eq_zero_of_le_zero (kOf_le_of_le (cov := cov) C hN hN hs.2.le)
  rw [hk0, datumAtR_zero]

/-- The value of the global field at the base time. -/
theorem parallelFieldR_zero (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b)
    (hN : 0 < C.N) (v₀ : E) :
    parallelFieldR (cov := cov) htor C hN v₀ (C.c 0) = frameVector (I := I) (C.x 0) (γ (C.c 0)) v₀ := by
  have hk0 : kOf (cov := cov) C hN (C.c 0) = 0 :=
    Nat.eq_zero_of_le_zero (kOf_le_of_le (cov := cov) C hN hN (C.mono 0 hN).le)
  rw [parallelFieldR, hk0, datumAtR_zero]
  show frameVector (I := I) (C.x 0) (γ (C.c 0)) (pieceSolR (cov := cov) htor C 0 v₀ (C.c 0)) = _
  exact congrArg (fun z => frameVector (I := I) (C.x 0) (γ (C.c 0)) z)
    (pieceSolR_datum (cov := cov) htor C hN v₀)

/-! ## §10 The overlap agreement of adjacent piece fields -/

/-- The junction lies strictly inside both rooms of a pair of adjacent pieces. -/
theorem c_lt_overlap (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k + 1 < C.N) :
    max (roomA C k) (roomA C (k + 1)) < C.c (k + 1) := by
  refine max_lt ?_ (roomA_lt_c (cov := cov) C hk)
  exact lt_of_lt_of_le (roomA_lt_c (cov := cov) C (k := k) (Nat.lt_of_succ_lt hk))
    (C.mono k (Nat.lt_of_succ_lt hk)).le

theorem c_lt_overlap' (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k + 1 < C.N) :
    C.c (k + 1) < min (roomB C k) (roomB C (k + 1)) :=
  lt_min (c_succ_lt_roomB (cov := cov) C (Nat.lt_of_succ_lt hk))
    (lt_trans (C.mono (k + 1) hk) (c_succ_lt_roomB (cov := cov) C hk))

/-- The two adjacent piece fields agree at the junction. -/
theorem pieceFieldR_junction (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k + 1 < C.N) (v : E) :
    pieceFieldR (cov := cov) htor C k v (C.c (k + 1))
      = pieceFieldR (cov := cov) htor C (k + 1) (nextDatumR (cov := cov) htor C k v)
          (C.c (k + 1)) := by
  have hsrc : γ (C.c (k + 1)) ∈ (chartAt H (C.x (k + 1))).source :=
    C.src (k + 1) hk (C.c (k + 1))
      (piece_subset_room (cov := cov) C hk ⟨le_rfl, (C.mono (k + 1) hk).le⟩)
  have hL : pieceFieldR (cov := cov) htor C k v (C.c (k + 1))
      = frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
          (Submission.JacobiCoords.chartCoords (I := I) (C.x (k + 1)) γ
            (pieceFieldR (cov := cov) htor C k v) (C.c (k + 1))) :=
    (Submission.JacobiCoords.frameVector_chartCoords (I := I) hsrc).symm
  have hR : pieceFieldR (cov := cov) htor C (k + 1) (nextDatumR (cov := cov) htor C k v)
        (C.c (k + 1))
      = frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
          (Submission.JacobiCoords.chartCoords (I := I) (C.x (k + 1)) γ
            (pieceFieldR (cov := cov) htor C k v) (C.c (k + 1))) := by
    show frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
        (pieceSolR (cov := cov) htor C (k + 1) (nextDatumR (cov := cov) htor C k v) (C.c (k + 1)))
      = frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
          (Submission.JacobiCoords.chartCoords (I := I) (C.x (k + 1)) γ
            (pieceFieldR (cov := cov) htor C k v) (C.c (k + 1)))
    congr 1
    exact pieceSolR_datum (cov := cov) htor C hk (nextDatumR (cov := cov) htor C k v)
  rw [hL, hR]

/-- **The overlap agreement** (pointwise form): adjacent piece fields agree on the intersection of
their rooms, by uniqueness of the parallel field (`eqOn_of_parallel`). -/
theorem pieceFieldR_overlap_on (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k + 1 < C.N) (v : E)
    (hγ1 : ∀ t ∈ Ioo (max (roomA C k) (roomA C (k + 1))) (min (roomB C k) (roomB C (k + 1))),
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ t ∈ Ioo (max (roomA C k) (roomA C (k + 1))) (min (roomB C k) (roomB C (k + 1))),
      curveVelocity (I := I) γ t ≠ 0)
    {s : ℝ} (hs : s ∈ Ioo (max (roomA C k) (roomA C (k + 1))) (min (roomB C k) (roomB C (k + 1)))) :
    pieceFieldR (cov := cov) htor C k v s
      = pieceFieldR (cov := cov) htor C (k + 1) (nextDatumR (cov := cov) htor C k v) s := by
  set α : ℝ := max (roomA C k) (roomA C (k + 1)) with hαdef
  set β : ℝ := min (roomB C k) (roomB C (k + 1)) with hβdef
  have hαβ : α < β := lt_of_lt_of_le (c_lt_overlap (cov := cov) C hk) (c_lt_overlap' (cov := cov) C hk).le
  have ht₀ : C.c (k + 1) ∈ Ioo α β := ⟨c_lt_overlap (cov := cov) C hk, c_lt_overlap' (cov := cov) C hk⟩
  have hklt : k < C.N := Nat.lt_of_succ_lt hk
  have hsubk : Ioo α β ⊆ Ioo (roomA C k) (roomB C k) := fun t ht =>
    ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hsubk1 : Ioo α β ⊆ Ioo (roomA C (k + 1)) (roomB C (k + 1)) := fun t ht =>
    ⟨lt_of_le_of_lt (le_max_right _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have heqon := eqOn_of_parallel (cov := cov) hmet htor hαβ ht₀ hγ1 hne
    (fun t ht => smoothAlongAt_pieceFieldR (cov := cov) htor C hklt v (hsubk ht))
    (fun t ht => smoothAlongAt_pieceFieldR (cov := cov) htor C hk
      (nextDatumR (cov := cov) htor C k v) (hsubk1 ht))
    (fun t ht => covAlong_eq_zero_of_germ (cov := cov) htor C hklt v (hsubk ht)
      (hγ1 t ht) (hne t ht)
      (smoothAlongAt_pieceFieldR (cov := cov) htor C hklt v (hsubk ht))
      (Filter.EventuallyEq.refl _ _))
    (fun t ht => covAlong_eq_zero_of_germ (cov := cov) htor C hk (nextDatumR (cov := cov) htor C k v)
      (hsubk1 ht) (hγ1 t ht) (hne t ht)
      (smoothAlongAt_pieceFieldR (cov := cov) htor C hk (nextDatumR (cov := cov) htor C k v)
        (hsubk1 ht)) (Filter.EventuallyEq.refl _ _))
    (pieceFieldR_junction (cov := cov) htor C hk v)
  exact heqon s hs

/-- **The germ of the global field at an interior junction is the *right* piece field**: at
`C.c (k+1)`, `parallelFieldR` agrees with `pieceFieldR C (k+1) (datumAtR (k+1))` on the
neighbourhood `Ioo (max α (C.c k)) (min β (C.c (k+2)))`. -/
theorem parallelFieldR_eventuallyEq_piece_succ (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (v₀ : E)
    {k : ℕ} (hk : k + 1 < C.N)
    (hγ1 : ∀ t ∈ Ioo (max (roomA C k) (roomA C (k + 1))) (min (roomB C k) (roomB C (k + 1))),
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ t ∈ Ioo (max (roomA C k) (roomA C (k + 1))) (min (roomB C k) (roomB C (k + 1))),
      curveVelocity (I := I) γ t ≠ 0) :
    parallelFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C hN v₀ =ᶠ[𝓝 (C.c (k + 1))]
      pieceFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C (k + 1)
        (datumAtR (cov := cov) htor C v₀ (k + 1)) := by
  have hklt : k < C.N := Nat.lt_of_succ_lt hk
  have hA : max (roomA C k) (roomA C (k + 1)) < C.c (k + 1) := c_lt_overlap (cov := cov) C hk
  have hB : C.c (k + 1) < min (roomB C k) (roomB C (k + 1)) := c_lt_overlap' (cov := cov) C hk
  refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds
    (show C.c (k + 1) ∈ Ioo (max (max (roomA C k) (roomA C (k + 1))) (C.c k))
      (min (min (roomB C k) (roomB C (k + 1))) (C.c (k + 2))) from
      ⟨max_lt hA (C.mono k hklt), lt_min hB (C.mono (k + 1) hk)⟩)) (fun s hs => ?_)
  rcases lt_trichotomy s (C.c (k + 1)) with hst | heq | hst
  · -- `s` left of the junction: piece `k`, then the overlap
    have hs1 : C.c k < s := lt_of_le_of_lt (le_max_right _ _) hs.1
    have hkof : kOf (cov := cov) C hN s = k := kOf_eq_of_mem (cov := cov) C hN hklt hs1 hst.le
    rw [parallelFieldR, hkof]
    have hovs : s ∈ Ioo (max (roomA C k) (roomA C (k + 1))) (min (roomB C k) (roomB C (k + 1))) :=
      ⟨lt_of_le_of_lt (le_max_left (max (roomA C k) (roomA C (k + 1))) (C.c k)) hs.1,
        lt_of_lt_of_le hst hB.le⟩
    rw [pieceFieldR_overlap_on (cov := cov) hmet htor C hk (datumAtR (cov := cov) htor C v₀ k)
      (fun u hu => hγ1 u hu) (fun u hu => hne u hu) hovs]
    rfl
  · -- at the junction
    subst heq
    have hkof : kOf (cov := cov) C hN (C.c (k + 1)) = k :=
      kOf_eq_of_mem (cov := cov) C hN hklt (C.mono k hklt) le_rfl
    rw [parallelFieldR, hkof]
    exact pieceFieldR_junction (cov := cov) htor C hk (datumAtR (cov := cov) htor C v₀ k)
  · -- `s` right of the junction: the piece `k+1`
    have hsub2 : s ≤ C.c (k + 2) := le_of_lt (lt_of_lt_of_le hs.2 (min_le_right _ _))
    have hkof : kOf (cov := cov) C hN s = k + 1 := kOf_eq_of_mem (cov := cov) C hN hk hst hsub2
    rw [parallelFieldR, hkof]

/-! ## §11 The germ of the global field is a piece field -/

/-- For `s > C.c (N-1)` the index `kOf` is the last one. -/
theorem kOf_eq_last (C : GeodesicCover cov γ a b) (hN : 0 < C.N) {s : ℝ}
    (hs : C.c (C.N - 1) < s) :
    kOf (cov := cov) C hN s = C.N - 1 := by
  refine le_antisymm (kOf_le (cov := cov) C hN s) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hspec := kOf_spec (cov := cov) C hN s
  have h1 : C.c (kOf (cov := cov) C hN s + 1) < C.c C.N := by
    refine c_mono_lt (cov := cov) C (by omega) le_rfl
  have h2 : C.c (kOf (cov := cov) C hN s + 1) ≤ C.c (C.N - 1) :=
    c_mono_le (cov := cov) C (by omega) (by omega)
  rcases le_total s (C.c C.N) with hle | hlt
  · rw [min_eq_left hle] at hspec
    exact absurd (le_trans hspec h2) (not_le.mpr hs)
  · rw [min_eq_right hlt] at hspec
    exact absurd (lt_of_le_of_lt hspec h1) (lt_irrefl (C.c C.N))

/-- For `t ∈ [a,b]` there is a piece `k < C.N` whose field has the same germ as
`parallelFieldR` at `t`, and `t` lies in the open room of that piece. -/
theorem parallelFieldR_eventuallyEq_some_piece (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (v₀ : E)
    (hγ1 : ∀ k < C.N, ∀ t ∈ Ioo (roomA C k) (roomB C k),
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ k < C.N, ∀ t ∈ Ioo (roomA C k) (roomB C k), curveVelocity (I := I) γ t ≠ 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ∃ k : ℕ, k < C.N ∧ t ∈ Ioo (roomA C k) (roomB C k) ∧
      parallelFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C hN v₀ =ᶠ[𝓝 t]
        pieceFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C k
          (datumAtR (cov := cov) htor C v₀ k) := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · -- `t = a = C.c 0`
    have hC : C.c 0 = t := C.c_zero.trans h
    refine ⟨0, hN, ?_, ?_⟩
    · exact hC ▸ ⟨roomA_lt_c (cov := cov) C (k := 0) hN,
        lt_trans (C.mono 0 hN) (c_succ_lt_roomB (cov := cov) C hN)⟩
    · exact hC ▸ parallelFieldR_eventuallyEq_piece_zero (cov := cov) htor C hN v₀
  · -- `a < t`
    have hb : t ≤ C.c C.N := by simpa [C.c_last] using ht.2
    set j : ℕ := kOf (cov := cov) C hN t with hjdef
    have hhi : t ≤ C.c (j + 1) := by rw [hjdef]; exact kOf_spec' (cov := cov) C hN hb
    have hklt : j < C.N := by rw [hjdef]; exact kOf_lt_N (cov := cov) C hN t
    have hlo : C.c j < t := by
      rw [hjdef]; exact c_kOf_lt_of_lt (cov := cov) C hN (by simpa [C.c_zero] using h)
    have hroom : t ∈ Ioo (roomA C j) (roomB C j) :=
      ⟨lt_of_lt_of_le (roomA_lt_c (cov := cov) C hklt) hlo.le,
        lt_of_le_of_lt hhi (c_succ_lt_roomB (cov := cov) C hklt)⟩
    rcases lt_or_eq_of_le hhi with hlt | heq
    · refine ⟨j, hklt, hroom, ?_⟩
      rw [hjdef]
      exact parallelFieldR_eventuallyEq_piece (cov := cov) htor C hN v₀ hklt hlo hlt
    · -- `t = C.c (j+1)`: a junction
      by_cases hk1 : j + 1 < C.N
      · refine ⟨j + 1, hk1, ?_, ?_⟩
        · rw [heq]
          exact ⟨roomA_lt_c (cov := cov) C hk1,
            lt_trans (C.mono (j + 1) hk1) (c_succ_lt_roomB (cov := cov) C hk1)⟩
        · rw [heq]
          exact parallelFieldR_eventuallyEq_piece_succ (cov := cov) hmet htor C hN v₀
            (k := j) hk1
            (fun u hu => hγ1 _ hk1 u ⟨lt_of_le_of_lt (le_max_right (roomA C j) (roomA C (j + 1))) hu.1,
              lt_of_lt_of_le hu.2 (min_le_right (roomB C j) (roomB C (j + 1)))⟩)
            (fun u hu => hne _ hk1 u ⟨lt_of_le_of_lt (le_max_right (roomA C j) (roomA C (j + 1))) hu.1,
              lt_of_lt_of_le hu.2 (min_le_right (roomB C j) (roomB C (j + 1)))⟩)
      · -- `j+1 = C.N`, i.e. `t = b`
        have hkN : j = C.N - 1 := by omega
        refine ⟨C.N - 1, by omega, ?_, ?_⟩
        · rw [← hkN]; exact hroom
        have hlo' : C.c (C.N - 1) < t := by rw [← hkN]; exact hlo
        refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds
            (show t ∈ Ioo (C.c (C.N - 1)) (t + 1) from ⟨hlo', by linarith⟩))
          (fun s hs => ?_)
        rcases le_total s (C.c C.N) with hs' | hs'
        · rw [parallelFieldR, kOf_eq_of_mem (cov := cov) C hN (by omega) hs.1
            (by rw [← Nat.sub_add_cancel hN] at hs'; exact hs')]
        · rw [parallelFieldR, kOf_eq_last (cov := cov) C hN hs.1]

/-! ## §12 The final properties of the global field on `[a,b]` -/

/-- **The global parallel field is smooth along `γ`** at every point of `[a,b]`. -/
theorem smoothAlongAt_parallelFieldR (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (v₀ : E)
    (hγ1 : ∀ k < C.N, ∀ t ∈ Ioo (roomA C k) (roomB C k),
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ k < C.N, ∀ t ∈ Ioo (roomA C k) (roomB C k), curveVelocity (I := I) γ t ≠ 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    SmoothAlongAt (I := I) γ
      (parallelFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C hN v₀) t := by
  obtain ⟨k, hk, hroom, hgerm⟩ :=
    parallelFieldR_eventuallyEq_some_piece (cov := cov) hmet htor C hN v₀ hγ1 hne ht
  exact SmoothAlongAt_congr (smoothAlongAt_pieceFieldR (cov := cov) htor C hk
    (datumAtR (cov := cov) htor C v₀ k) hroom) hgerm.symm

/-- **The global parallel field is parallel along `γ`** at every point of `[a,b]`. -/
theorem covAlong_parallelFieldR (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (v₀ : E)
    (hγ1 : ∀ k < C.N, ∀ t ∈ Ioo (roomA C k) (roomB C k),
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ k < C.N, ∀ t ∈ Ioo (roomA C k) (roomB C k), curveVelocity (I := I) γ t ≠ 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    covAlong cov (parallelFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C hN v₀) t = 0 := by
  obtain ⟨k, hk, hroom, hgerm⟩ :=
    parallelFieldR_eventuallyEq_some_piece (cov := cov) hmet htor C hN v₀ hγ1 hne ht
  exact covAlong_eq_zero_of_germ (cov := cov) htor C hk (datumAtR (cov := cov) htor C v₀ k)
    hroom (hγ1 k hk t hroom) (hne k hk t hroom)
    (smoothAlongAt_parallelFieldR (cov := cov) hmet htor C hN v₀ hγ1 hne ht) hgerm

/-- The whole package: the global field is smooth along `γ` and parallel on `[a,b]`. -/
theorem parallelFieldR_spec (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (v₀ : E)
    (hγ1 : ∀ k < C.N, ∀ t ∈ Ioo (roomA C k) (roomB C k),
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : ∀ k < C.N, ∀ t ∈ Ioo (roomA C k) (roomB C k), curveVelocity (I := I) γ t ≠ 0) :
    (∀ t ∈ Icc a b, SmoothAlongAt (I := I) γ
        (parallelFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C hN v₀) t) ∧
      (∀ t ∈ Icc a b, covAlong cov
        (parallelFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C hN v₀) t = 0) :=
  ⟨fun t ht => smoothAlongAt_parallelFieldR (cov := cov) hmet htor C hN v₀ hγ1 hne ht,
   fun t ht => covAlong_parallelFieldR (cov := cov) hmet htor C hN v₀ hγ1 hne ht⟩

end

end Submission.ParallelRoom
