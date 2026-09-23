import Submission.ChartPieces
import Submission.ChartIndep
import Submission.Commons.Analysis.Calculus.contDiffAt_one_of_hasDerivAt
import Submission.ParallelField
import Submission.IndexCorner2
import Submission.Commons.Analysis.ODE.exists_linearODE_solution_Icc

/-!
# The global parallel field along a geodesic

`Submission.ParallelField` provides the parallel field **within one chart**: the solution of
`y' = -Γ̂ y` on an interval.  This file glues those solutions over the finite chart cover of a
geodesic (`Submission.ChartPieces.exists_chart_pieces`) into a **global** field along the geodesic.
This is item **(P)** of `Submission/Roadmap.lean` §110.6: the first rung of the Synge/holonomy
chapter, and the source of the parallel normal fields that the index estimate of
§110.4.4 needs.

Contents (namespace `Submission.ParallelGlobal`):

* **`exists_parallelChart`** — the chart-level parallel equation `y' = -Γ̂ y` on `[a,b]` with a
  prescribed datum at the **left** endpoint, existence + uniqueness, with *weak* hypotheses
  (continuity of the chart data only, no geodesic equation needed);
* `parallelChart_add` — the chart-level solution depends *linearly* on the initial datum;
* **`GeodesicCover`** — the bundled chart cover of a geodesic on `[a,b]` (partition, charts, room,
  source membership and the chart geodesic ODE), with the producer **`exists_geodesicCover`**;
* `pieceSol`, `datumAt`, `pathCoords`, **`parallelField`** — the piecewise construction: on each
  piece the field is the chart-level solution, and the datum of the next piece is the **converted
  value** produced by the previous one;
* `parallelField_piece`, `datumAt_add`, `datumAt_smul`, `parallelField_add`, `parallelField_smul` —
  the field is *linear* in the initial datum;
* `chartGram_pieceSol_closed` — the chart Gram form of the piece solution is constant on the
  **closed** piece; `gram_datumAt` — the Gram form of the datum is independent of the piece;
* **`norm_parallelField` / `norm_parallelField_sq`** — the field has **constant norm**: the transport
  is an **isometry**;
* **`parallelField_add` / `parallelField_smul`** — the transport is **linear** in the datum (via
  `pieceSol_add`/`pieceSol_smul`, `pieceField_add`/`pieceField_smul`, `nextDatum_add`/`nextDatum_smul`
  and `datumAt_add`/`datumAt_smul`);
* **`pieceSol_deriv`** — the chart velocity of a geodesic is **parallel along it** (the geodesic
  field solves `y' = -Γ̂ y`), i.e. a geodesic is parallel along itself.

This is the full **parallel transport** chapter (Mathlib has none): existence, uniqueness, linearity
and the isometry property, plus the fact that the velocity is a parallel field.  What remains for the
*holonomy of a closed geodesic* is only the bookkeeping of the endpoint (`γ b = γ a`), and for
**Synge's lemma** the orientation statement `det = 1` (see `Submission/Roadmap.lean` §112).
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

namespace Submission.ParallelGlobal

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

/-! ## §1 The chart-level parallel equation -/

/-- **The chart-level parallel equation** `y' = -Γ̂ y` on `[a,b]`, with datum `y₀` at the *left*
endpoint `a`: existence and uniqueness.  Only continuity of the chart data is needed (no geodesic
equation): the coefficient `t ↦ -gammaOp x₀ u w t` is continuous on `[a,b]`. -/
theorem exists_parallelChart (htor : cov.torsion = 0)
    {x₀ : M} {u w : ℝ → E} {a b : ℝ} (hab : a < b)
    (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) (y₀ : E) :
    ∃ y : ℝ → E,
      y a = y₀ ∧ (∀ t ∈ Icc a b, HasDerivAt y
        (-(gammaOp (cov := cov) x₀ u w t (y t))) t) ∧
      ∀ z : ℝ → E, z a = y₀ →
        (∀ t ∈ Icc a b, HasDerivAt z (-(gammaOp (cov := cov) x₀ u w t (z t))) t) →
        EqOn z y (Icc a b) := by
  have hA : ContinuousOn (fun t : ℝ => -(gammaOp (cov := cov) x₀ u w t)) (Icc a b) :=
    (Submission.IndexCorner2.continuousOn_gammaOp_of_cont (cov := cov) htor hu hw htgt).neg
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨y, hy0, hyd, hyu⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc (E := E) hab hA ha y₀
  exact ⟨y, hy0, hyd, fun z hz0 hz => hyu z hz0 hz⟩

/-- The chart-level parallel solution is **additive** in the initial datum. -/
theorem parallelChart_add (htor : cov.torsion = 0)
    {x₀ : M} {u w : ℝ → E} {a b : ℝ} (hab : a < b)
    (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target)
    {y z : ℝ → E} (hy : ∀ t ∈ Icc a b,
      HasDerivAt y (-(gammaOp (cov := cov) x₀ u w t (y t))) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (-(gammaOp (cov := cov) x₀ u w t (z t))) t) :
    ∀ t ∈ Icc a b, HasDerivAt (fun s => y s + z s)
      (-(gammaOp (cov := cov) x₀ u w t ((fun s => y s + z s) t))) t := by
  intro t ht
  have h := (hy t ht).add (hz t ht)
  have hval : -(gammaOp (cov := cov) x₀ u w t (y t))
      + -(gammaOp (cov := cov) x₀ u w t (z t))
      = -(gammaOp (cov := cov) x₀ u w t ((fun s => y s + z s) t)) := by
    rw [map_add, neg_add]
  rw [hval] at h
  exact h

/-- The chart-level parallel solution is **homogeneous** in the initial datum. -/
theorem parallelChart_smul (htor : cov.torsion = 0)
    {x₀ : M} {u w : ℝ → E} {a b : ℝ} (hab : a < b)
    (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target)
    {y : ℝ → E} (hy : ∀ t ∈ Icc a b,
      HasDerivAt y (-(gammaOp (cov := cov) x₀ u w t (y t))) t) (c : ℝ) :
    ∀ t ∈ Icc a b, HasDerivAt (fun s => c • y s)
      (-(gammaOp (cov := cov) x₀ u w t ((fun s => c • y s) t))) t := by
  intro t ht
  have h := (hy t ht).const_smul c
  have hval : c • -(gammaOp (cov := cov) x₀ u w t (y t))
      = -(gammaOp (cov := cov) x₀ u w t ((fun s => c • y s) t)) := by
    rw [map_smul, smul_neg]
  rw [hval] at h
  exact h

/-! ## §2 The chart cover of a geodesic -/

/-- **A chart cover of a geodesic on `[a,b]`**: a partition `a = c 0 < ⋯ < c N = b`, charts `x k`
and open intervals `Ioo (A k) (B k)` with room around each piece, on which `γ` stays in the chart
source and satisfies the chart geodesic equation.  This is exactly the output of
`Submission.ChartPieces.exists_chart_pieces`, bundled. -/
structure GeodesicCover (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (γ : ℝ → M) (a b : ℝ) where
  N : ℕ
  c : ℕ → ℝ
  x : ℕ → M
  A : ℕ → ℝ
  B : ℕ → ℝ
  c_zero : c 0 = a
  c_last : c N = b
  mono : ∀ k : ℕ, k < N → c k < c (k + 1)
  room : ∀ k : ℕ, k < N → A k < c k ∧ c (k + 1) < B k
  src : ∀ k : ℕ, k < N → ∀ t ∈ Set.Ioo (A k) (B k), γ t ∈ (chartAt H (x k)).source
  ode : ∀ k : ℕ, k < N → ∀ t ∈ Set.Ioo (A k) (B k),
      HasDerivAt (fun s => (extChartAt I (x k)) (γ s))
        (deriv (fun s => (extChartAt I (x k)) (γ s)) t) t ∧
      HasDerivAt (deriv (fun s => (extChartAt I (x k)) (γ s)))
        (chartGeodesicVectorField cov (x k)
          ((extChartAt I (x k)) (γ t),
            deriv (fun s => (extChartAt I (x k)) (γ s)) t)) t

variable {γ : ℝ → M} {a b : ℝ}

/-- The chart cover of a geodesic exists, by `Submission.ChartPieces.exists_chart_pieces`. -/
theorem exists_geodesicCover (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {V : Set ℝ} (hV : IsOpen V) (hab : a ≤ b) (hVab : Icc a b ⊆ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hgeo : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0) :
    Nonempty (GeodesicCover cov γ a b) := by
  obtain ⟨N, c, hc0, hcN, hmono, x, A, B, hroom, hsrc, hode⟩ :=
    Submission.ChartPieces.exists_chart_pieces cov hV hab hVab hγ hgeo hne
  refine ⟨{ N := N, c := c, x := x, A := A, B := B, c_zero := hc0, c_last := hcN, mono := hmono, room := hroom, src := hsrc, ode := hode }⟩

/-- The piece `[c k, c (k+1)]` is contained in the open interval of validity `Ioo (A k) (B k)`. -/
theorem piece_subset_room (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    Icc (C.c k) (C.c (k + 1)) ⊆ Set.Ioo (C.A k) (C.B k) :=
  fun t ht => ⟨lt_of_lt_of_le (C.room k hk).1 ht.1, lt_of_le_of_lt ht.2 (C.room k hk).2⟩

/-- The chart coordinates of `γ` on a piece are continuous. -/
theorem continuousOn_chartCoord_piece (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    ContinuousOn (fun t : ℝ => (extChartAt I (C.x k)) (γ t)) (Icc (C.c k) (C.c (k + 1))) := by
  have h1 : DifferentiableOn ℝ (fun t : ℝ => (extChartAt I (C.x k)) (γ t))
      (Set.Ioo (C.A k) (C.B k)) := fun t ht =>
    ((C.ode k hk t ht).1).differentiableAt.differentiableWithinAt
  exact (h1.continuousOn).mono (piece_subset_room (cov := cov) C hk)

/-- The chart velocity of `γ` on a piece is continuous. -/
theorem continuousOn_deriv_chartCoord_piece (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    ContinuousOn (deriv (fun t : ℝ => (extChartAt I (C.x k)) (γ t)))
      (Icc (C.c k) (C.c (k + 1))) := by
  have h1 : DifferentiableOn ℝ (deriv (fun t : ℝ => (extChartAt I (C.x k)) (γ t)))
      (Set.Ioo (C.A k) (C.B k)) := fun t ht =>
    ((C.ode k hk t ht).2).differentiableAt.differentiableWithinAt
  exact (h1.continuousOn).mono (piece_subset_room (cov := cov) C hk)

/-- On a piece, the chart coordinates of `γ` lie in the chart target. -/
theorem chartCoord_mem_target_piece (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    ∀ t ∈ Icc (C.c k) (C.c (k + 1)),
      (extChartAt I (C.x k)) (γ t) ∈ (extChartAt I (C.x k)).target := by
  intro t ht
  have hsrc : γ t ∈ (extChartAt I (C.x k)).source := by
    rw [extChartAt_source]
    exact C.src k hk t (piece_subset_room (cov := cov) C hk ht)
  exact (extChartAt I (C.x k)).map_source hsrc

/-! ## §3 The piecewise parallel field -/

section Cover

variable (htor : cov.torsion = 0)

/-- The chart-level parallel solution on piece `k`, with datum `v` at the *left* endpoint `c k`
(junk value `0` for `k ≥ N`). -/
noncomputable def pieceSol (C : GeodesicCover cov γ a b) (k : ℕ) (v : E) : ℝ → E :=
  if hk : k < C.N then
    Classical.choose (exists_parallelChart (cov := cov) htor (C.mono k hk)
      (continuousOn_chartCoord_piece (cov := cov) C hk)
      (continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
      (chartCoord_mem_target_piece (cov := cov) C hk) v)
  else fun _ => 0

/-- The chart-`x k` coordinate curve of `γ`, written once and for all. -/
noncomputable def coordCurve (C : GeodesicCover cov γ a b) (k : ℕ) : ℝ → E :=
  fun t => (extChartAt I (C.x k)) (γ t)

theorem pieceSol_eq_choose (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) (v : E) :
    pieceSol htor C k v = Classical.choose (exists_parallelChart (cov := cov) htor
      (C.mono k hk) (continuousOn_chartCoord_piece (cov := cov) C hk)
      (continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
      (chartCoord_mem_target_piece (cov := cov) C hk) v) := by
  rw [pieceSol, dif_pos hk]

/-- The datum of the piece solution. -/
theorem pieceSol_datum (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) (v : E) :
    pieceSol htor C k v (C.c k) = v := by
  rw [pieceSol_eq_choose (cov := cov) htor C hk v]
  exact (Classical.choose_spec (exists_parallelChart (cov := cov) htor (C.mono k hk)
    (continuousOn_chartCoord_piece (cov := cov) C hk)
    (continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
    (chartCoord_mem_target_piece (cov := cov) C hk) v)).1

/-- The piece solution satisfies the parallel equation `y' = -Γ̂ y` on the piece. -/
theorem pieceSol_ode (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) (v : E) :
    ∀ t ∈ Icc (C.c k) (C.c (k + 1)), HasDerivAt (pieceSol htor C k v)
      (-(gammaOp (cov := cov) (C.x k) (coordCurve (I := I) C k)
        (deriv (coordCurve (I := I) C k)) t (pieceSol htor C k v t))) t := by
  rw [pieceSol_eq_choose (cov := cov) htor C hk v]
  exact (Classical.choose_spec (exists_parallelChart (cov := cov) htor (C.mono k hk)
    (continuousOn_chartCoord_piece (cov := cov) C hk)
    (continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
    (chartCoord_mem_target_piece (cov := cov) C hk) v)).2.1

/-- Uniqueness for the piece solution. -/
theorem pieceSol_unique (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) (v : E)
    {z : ℝ → E} (hz : z (C.c k) = v)
    (hzode : ∀ t ∈ Icc (C.c k) (C.c (k + 1)), HasDerivAt z
      (-(gammaOp (cov := cov) (C.x k) (coordCurve (I := I) C k)
        (deriv (coordCurve (I := I) C k)) t (z t))) t) :
    EqOn z (pieceSol htor C k v) (Icc (C.c k) (C.c (k + 1))) := by
  rw [pieceSol_eq_choose (cov := cov) htor C hk v]
  exact (Classical.choose_spec (exists_parallelChart (cov := cov) htor (C.mono k hk)
    (continuousOn_chartCoord_piece (cov := cov) C hk)
    (continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
    (chartCoord_mem_target_piece (cov := cov) C hk) v)).2.2 z hz hzode

/-- **Linearity in the datum** (addition). -/
theorem pieceSol_add (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) (v w : E) :
    EqOn (fun t => pieceSol htor C k v t + pieceSol htor C k w t)
      (pieceSol htor C k (v + w)) (Icc (C.c k) (C.c (k + 1))) := by
  refine pieceSol_unique (cov := cov) htor C hk (v + w) ?_ ?_
  · show pieceSol htor C k v (C.c k) + pieceSol htor C k w (C.c k) = v + w
    rw [pieceSol_datum (cov := cov) htor C hk v, pieceSol_datum (cov := cov) htor C hk w]
  · exact parallelChart_add (cov := cov) htor (C.mono k hk)
      (continuousOn_chartCoord_piece (cov := cov) C hk)
      (continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
      (chartCoord_mem_target_piece (cov := cov) C hk)
      (pieceSol_ode (cov := cov) htor C hk v) (pieceSol_ode (cov := cov) htor C hk w)

/-- **Linearity in the datum** (scalar multiplication). -/
theorem pieceSol_smul (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) (c : ℝ) (v : E) :
    EqOn (fun t => c • pieceSol htor C k v t) (pieceSol htor C k (c • v))
      (Icc (C.c k) (C.c (k + 1))) := by
  refine pieceSol_unique (cov := cov) htor C hk (c • v) ?_ ?_
  · show c • pieceSol htor C k v (C.c k) = c • v
    rw [pieceSol_datum (cov := cov) htor C hk v]
  · exact parallelChart_smul (cov := cov) htor (C.mono k hk)
      (continuousOn_chartCoord_piece (cov := cov) C hk)
      (continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
      (chartCoord_mem_target_piece (cov := cov) C hk)
      (pieceSol_ode (cov := cov) htor C hk v) c

end Cover

/-! ## §4 The piece fields, their junctions, and the global field -/

section Global

variable (htor : cov.torsion = 0)

/-- **The field along `γ` produced by piece `k` with datum `v`**: the frame vector of the chart-level
parallel solution. -/
noncomputable def pieceField (C : GeodesicCover cov γ a b) (k : ℕ) (v : E) :
    (t : ℝ) → TangentSpace I (γ t) :=
  fun t => frameVector (I := I) (C.x k) (γ t) (pieceSol htor C k v t)

/-- The covariant derivative of a piece solution vanishes on the piece. -/
theorem pieceSol_covDeriv (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) (v : E) :
    ∀ t ∈ Icc (C.c k) (C.c (k + 1)),
      chartCovDeriv cov (C.x k) (coordCurve (I := I) C k) (deriv (coordCurve (I := I) C k))
        (pieceSol htor C k v) t = 0 :=
  fun t ht => Submission.ParallelField.chartCovDeriv_eq_zero_iff (cov := cov)
    ((chartCoord_mem_target_piece (cov := cov) C hk) t ht)
    (pieceSol_ode (cov := cov) htor C hk v t ht)

/-- **The datum of the next piece**: the chart-`x (k+1)` coordinates of the value produced by
piece `k` at the junction. -/
noncomputable def nextDatum (C : GeodesicCover cov γ a b) (k : ℕ) (v : E) : E :=
  Submission.JacobiCoords.chartCoords (I := I) (C.x (k + 1)) γ
    (pieceField (cov := cov) htor C k v) (C.c (k + 1))

/-- **The junction condition**: the field of piece `k` and the field of piece `k+1` with the
converted datum agree at the junction. -/
theorem pieceField_junction (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k + 1 < C.N) (v : E) :
    pieceField (cov := cov) htor C k v (C.c (k + 1))
      = pieceField (cov := cov) htor C (k + 1)
          (nextDatum (cov := cov) htor C k v) (C.c (k + 1)) := by
  have hsrc : γ (C.c (k + 1)) ∈ (chartAt H (C.x (k + 1))).source :=
    C.src (k + 1) hk (C.c (k + 1))
      (piece_subset_room (cov := cov) C hk ⟨le_rfl, (C.mono (k + 1) hk).le⟩)
  have hL : pieceField (cov := cov) htor C k v (C.c (k + 1))
      = frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
          (Submission.JacobiCoords.chartCoords (I := I) (C.x (k + 1)) γ
            (pieceField (cov := cov) htor C k v) (C.c (k + 1))) :=
    (Submission.JacobiCoords.frameVector_chartCoords (I := I) hsrc).symm
  have hR : pieceField (cov := cov) htor C (k + 1)
        (nextDatum (cov := cov) htor C k v) (C.c (k + 1))
      = frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
          (Submission.JacobiCoords.chartCoords (I := I) (C.x (k + 1)) γ
            (pieceField (cov := cov) htor C k v) (C.c (k + 1))) := by
    show frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
        (pieceSol htor C (k + 1) (nextDatum (cov := cov) htor C k v) (C.c (k + 1)))
      = frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
          (Submission.JacobiCoords.chartCoords (I := I) (C.x (k + 1)) γ
            (pieceField (cov := cov) htor C k v) (C.c (k + 1)))
    congr 1
    exact pieceSol_datum (cov := cov) htor C hk (nextDatum (cov := cov) htor C k v)
  rw [hL, hR]

end Global

/-! ## §5 The global parallel field along the geodesic -/

section Assemble

variable (htor : cov.torsion = 0)

/-- Monotonicity of the partition, on `[0,N]`. -/
theorem c_mono_le (C : GeodesicCover cov γ a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ C.N) :
    C.c i ≤ C.c j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact le_trans (ih (Nat.le_of_succ_le hj)) (C.mono j (Nat.lt_of_succ_le hj)).le

/-- The datum of every piece, obtained by the recursion: the datum of piece `k+1` is the converted
value produced by piece `k` at the junction. -/
noncomputable def datumAt (C : GeodesicCover cov γ a b) (v₀ : E) : ℕ → E :=
  Nat.rec v₀ (fun k v => nextDatum (cov := cov) htor C k v)

theorem datumAt_zero (C : GeodesicCover cov γ a b) (v₀ : E) :
    datumAt htor C v₀ 0 = v₀ := rfl

theorem datumAt_succ (C : GeodesicCover cov γ a b) (v₀ : E) (k : ℕ) :
    datumAt htor C v₀ (k + 1)
      = nextDatum (cov := cov) htor C k (datumAt htor C v₀ k) := rfl

/-- The existence of the piece index (witness `N-1`). -/
theorem kOfExists (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (t : ℝ) :
    ∃ k : ℕ, min t (C.c C.N) ≤ C.c (k + 1) :=
  ⟨C.N - 1, by rw [Nat.sub_add_cancel hN]; exact min_le_right _ _⟩

/-- The index of the piece containing `t` (the least `k` with `min t b ≤ c (k+1)`). -/
noncomputable def kOf (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (t : ℝ) : ℕ :=
  Nat.find (kOfExists (cov := cov) C hN t)

theorem kOf_spec (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (t : ℝ) :
    min t (C.c C.N) ≤ C.c (kOf (cov := cov) C hN t + 1) :=
  Nat.find_spec (kOfExists (cov := cov) C hN t)

/-- For `t ≤ b` the piece index really is the least `k` with `t ≤ c (k+1)`. -/
theorem kOf_spec' (C : GeodesicCover cov γ a b) (hN : 0 < C.N) {t : ℝ}
    (ht : t ≤ C.c C.N) : t ≤ C.c (kOf (cov := cov) C hN t + 1) :=
  le_trans (le_min le_rfl ht) (kOf_spec (cov := cov) C hN t)

theorem kOf_le (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (t : ℝ) :
    kOf (cov := cov) C hN t ≤ C.N - 1 :=
  Nat.find_min' (kOfExists (cov := cov) C hN t)
    (by rw [Nat.sub_add_cancel hN]; exact min_le_right _ _)

theorem kOf_min (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (t : ℝ) {k : ℕ}
    (hk : k < kOf (cov := cov) C hN t) :
    ¬ (min t (C.c C.N) ≤ C.c (k + 1)) :=
  Nat.find_min (kOfExists (cov := cov) C hN t) hk

theorem kOf_le_of_le (C : GeodesicCover cov γ a b) (hN : 0 < C.N) {t : ℝ} {k : ℕ}
    (hk : k < C.N) (ht : t ≤ C.c (k + 1)) : kOf (cov := cov) C hN t ≤ k :=
  Nat.find_min' (kOfExists (cov := cov) C hN t) (le_trans (min_le_left _ _) ht)

/-- **The piece index of a point in the *interior* of a piece is that piece.**  (At the left
endpoint `c k` the convention `min t b ≤ c (k+1)` selects the previous piece; the two values agree
there by `pieceField_junction`.) -/
theorem kOf_eq_of_mem (C : GeodesicCover cov γ a b) (hN : 0 < C.N) {t : ℝ} {k : ℕ}
    (hk : k < C.N) (hlo : C.c k < t) (hhi : t ≤ C.c (k + 1)) :
    kOf (cov := cov) C hN t = k := by
  have htb : t ≤ C.c C.N := le_trans hhi (c_mono_le (cov := cov) C (Nat.succ_le_iff.mpr hk) le_rfl)
  have hmint : min t (C.c C.N) = t := min_eq_left htb
  -- any `m < k` fails the predicate
  have hnot : ∀ m < k, ¬ (min t (C.c C.N) ≤ C.c (m + 1)) := by
    intro m hm hp
    have h1 : t ≤ C.c (m + 1) := by
      have h2 := hp
      rw [hmint] at h2
      exact h2
    have h3 : C.c (m + 1) ≤ C.c k :=
      c_mono_le (cov := cov) C (Nat.succ_le_of_lt hm) hk.le
    linarith
  refine le_antisymm (kOf_le_of_le (cov := cov) C hN hk hhi) ?_
  by_contra hcon
  exact (hnot (kOf (cov := cov) C hN t) (not_le.mp hcon))
    (kOf_spec (cov := cov) C hN t)

/-- **The global parallel field along the geodesic** with datum `v₀` (the chart-`x 0` coordinates at
`t = a`): on the piece `k` it is the chart-level parallel solution with datum `datumAt k`. -/
noncomputable def parallelField (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (v₀ : E) :
    (t : ℝ) → TangentSpace I (γ t) :=
  fun t => pieceField (cov := cov) htor C (kOf (cov := cov) C hN t)
    (datumAt htor C v₀ (kOf (cov := cov) C hN t)) t

/-- **The datum of the global field** (stated at the base time `c 0`, which is `a` by
`C.c_zero`: point-level rewriting across that equality is awkward because the structure is
parameterised by `a`). -/
theorem parallelField_datum (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (v₀ : E) :
    parallelField (cov := cov) htor C hN v₀ (C.c 0)
      = frameVector (I := I) (C.x 0) (γ (C.c 0)) v₀ := by
  have hk0 : kOf (cov := cov) C hN (C.c 0) = 0 := by
    refine Nat.le_zero.mp (kOf_le_of_le (cov := cov) C hN hN ?_)
    exact (C.mono 0 hN).le
  show frameVector (I := I) (C.x (kOf (cov := cov) C hN (C.c 0))) (γ (C.c 0))
      (pieceSol htor C (kOf (cov := cov) C hN (C.c 0))
        (datumAt htor C v₀ (kOf (cov := cov) C hN (C.c 0))) (C.c 0))
    = frameVector (I := I) (C.x 0) (γ (C.c 0)) v₀
  rw [hk0, datumAt_zero (cov := cov) htor C v₀]
  exact congrArg (fun z => frameVector (I := I) (C.x 0) (γ (C.c 0)) z)
    (pieceSol_datum (cov := cov) htor C hN v₀)

/-- **The global field on a piece is the piece level solution.** -/
theorem parallelField_piece (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (v₀ : E) {k : ℕ}
    (hk : k < C.N) {t : ℝ} (hlo : C.c k < t) (hhi : t ≤ C.c (k + 1)) :
    parallelField (cov := cov) htor C hN v₀ t
      = pieceField (cov := cov) htor C k (datumAt htor C v₀ k) t := by
  rw [parallelField, kOf_eq_of_mem (cov := cov) C hN hk hlo hhi]

end Assemble

/-! ## §6 The transport is an isometry

The content of this section is the **Gram-form constancy** of the parallel field.  At the level of a
*single piece* it is exactly `Submission.ParallelField.chartGram_self_parallelField_eq`, transferred
from the chart curve `(extChartAt I (C.x k)).symm ∘ coordCurve` to the abstract curve `γ`.

**Remaining for the full isometry statement** (recorded in `Submission/Roadmap.lean` §111):

* the extension from the *open* piece `Ioo (c k) (c (k+1))` to the closed piece `Icc (c k)
  (c (k+1))` — by `BonnetMyers.continuousOn_chartGram_curve` plus uniqueness of limits;
* the chain over the pieces (using `pieceField_junction`, which makes the norm continuous across the
  junctions) producing `‖parallelField … v₀ t‖ = ‖frameVector x₀ (γ (c 0)) v₀‖` for `t ∈ [a,b]`;
* the *linearity* of `parallelField` in `v₀` (induction on the piece index, from `pieceSol_add`,
  `pieceSol_smul`, `frameVector_add`/`frameVector_smul` and the additivity of `chartCoords`). -/

section Isometry

variable (htor : cov.torsion = 0)

/-- The chart-`x k` coordinate curve of `γ` really is the curve `γ` re-read in the chart. -/
theorem eq_chartCurve_of_mem (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) {t : ℝ}
    (ht : t ∈ Ioo (C.c k) (C.c (k + 1))) :
    γ t = (extChartAt I (C.x k)).symm (coordCurve (I := I) C k t) := by
  have hsrc : γ t ∈ (extChartAt I (C.x k)).source := by
    rw [extChartAt_source]
    exact C.src k hk t (piece_subset_room (cov := cov) C hk ⟨ht.1.le, ht.2.le⟩)
  exact (PartialEquiv.left_inv (extChartAt I (C.x k)) hsrc).symm

/-- **The Gram form of the piece solution is constant on the open piece** (the chart-level
isometry statement `ParallelField.chartGram_self_parallelField_eq`, transferred to `γ`). -/
theorem chartGram_pieceSol_open (hmet : IsMetricCompatible cov) (C : GeodesicCover cov γ a b)
    {k : ℕ} (hk : k < C.N) (v : E) :
    ∀ t₁ ∈ Ioo (C.c k) (C.c (k + 1)), ∀ t₂ ∈ Ioo (C.c k) (C.c (k + 1)),
      Submission.ChartConnection.chartGram (I := I) (C.x k) (γ t₁)
          (pieceSol htor C k v t₁) (pieceSol htor C k v t₁)
        = Submission.ChartConnection.chartGram (I := I) (C.x k) (γ t₂)
            (pieceSol htor C k v t₂) (pieceSol htor C k v t₂) := by
  have hsub : Ioo (C.c k) (C.c (k + 1)) ⊆ Ioo (C.A k) (C.B k) := fun t ht =>
    piece_subset_room (cov := cov) C hk ⟨ht.1.le, ht.2.le⟩
  -- the chart-level hypotheses
  have hu : ∀ t ∈ Ioo (C.c k) (C.c (k + 1)),
      HasDerivAt (coordCurve (I := I) C k) (deriv (coordCurve (I := I) C k) t) t :=
    fun t ht => (C.ode k hk t (hsub ht)).1
  have hstay : ∀ t ∈ Ioo (C.c k) (C.c (k + 1)),
      coordCurve (I := I) C k t ∈ (extChartAt I (C.x k)).target := fun t ht =>
    (chartCoord_mem_target_piece (cov := cov) C hk t ⟨ht.1.le, ht.2.le⟩)
  have hX : ∀ t ∈ Ioo (C.c k) (C.c (k + 1)),
      HasDerivAt (pieceSol htor C k v) (deriv (pieceSol htor C k v) t) t := by
    intro t ht
    have h := pieceSol_ode (cov := cov) htor C hk v t ⟨ht.1.le, ht.2.le⟩
    rw [h.deriv]
    exact h
  have hpX : ∀ t ∈ Ioo (C.c k) (C.c (k + 1)),
      chartCovDeriv cov (C.x k) (coordCurve (I := I) C k) (deriv (coordCurve (I := I) C k))
        (pieceSol htor C k v) t = 0 := fun t ht =>
    pieceSol_covDeriv (cov := cov) htor C hk v t ⟨ht.1.le, ht.2.le⟩
  intro t₁ ht₁ t₂ ht₂
  have h := Submission.ParallelField.chartGram_self_parallelField_eq (cov := cov) hmet
    (x₀ := C.x k) hu hstay hX hpX t₁ ht₁ t₂ ht₂
  rw [← eq_chartCurve_of_mem (cov := cov) C hk ht₁,
    ← eq_chartCurve_of_mem (cov := cov) C hk ht₂] at h
  exact h

end Isometry

/-! ## §7 The transport is an isometry and is linear in the datum (DONE).

See the sections below for the statements and proofs:

* the Gram form of a piece solution is constant on the **closed** piece (`chartGram_pieceSol_closed`,
  via `Set.EqOn.of_subset_closure` + `BonnetMyers.continuousOn_chartGram_curve` + continuity of `γ`,
  which is `continuousOn_gamma_piece`), and the Gram form of the datum is independent of the piece
  (`gram_datumAt_succ` + `gram_datumAt`);
* hence the **norm** of `parallelField` is constant (`norm_parallelField_sq`, `norm_parallelField`):
  **the parallel transport is an isometry**;
* the **linearity** of the global field in the datum (`parallelField_add`, `parallelField_smul`)
  follows from the chart-level linearity (`parallelChart_add`/`_smul`), the piece-level linearity
  (`pieceSol_add`/`_smul`), the additivity of the datum conversion (`nextDatum_add`/`_smul`) and of
  the datum recursion (`datumAt_add`/`_smul`), using the two bounds `c (kOf t) ≤ t ≤ c (kOf t + 1)`
  (`c_kOf_le`, `kOf_spec'`) and `kOf_lt`.

The last section proves that **the chart velocity of a geodesic is parallel along it**
(`pieceSol_deriv`), via `chartGeodesicVectorField_eq_neg_gammaOp`. -/


/-- The geodesic is continuous on a piece. -/
theorem continuousOn_gamma_piece (C : GeodesicCover cov γ a b) {k : ℕ} (hk : k < C.N) :
    ContinuousOn γ (Icc (C.c k) (C.c (k + 1))) := by
  have hmem : ∀ t ∈ Icc (C.c k) (C.c (k + 1)),
      γ t ∈ (extChartAt I (C.x k)).source := by
    intro t ht
    rw [extChartAt_source]
    exact C.src k hk t (piece_subset_room (cov := cov) C hk ht)
  have h1 : ContinuousOn (fun t : ℝ => (extChartAt I (C.x k)) (γ t))
      (Icc (C.c k) (C.c (k + 1))) := continuousOn_chartCoord_piece (cov := cov) C hk
  have h2 : ContinuousOn
      (fun t : ℝ => (extChartAt I (C.x k)).symm ((extChartAt I (C.x k)) (γ t)))
      (Icc (C.c k) (C.c (k + 1))) :=
    (continuousOn_extChartAt_symm (I := I) (C.x k)).comp h1
      (fun t ht => chartCoord_mem_target_piece (cov := cov) C hk t ht)
  refine h2.congr (fun t ht => ?_)
  exact (PartialEquiv.left_inv (extChartAt I (C.x k)) (hmem t ht)).symm

/-- **The Gram form of the piece solution is constant on the closed piece.** -/
theorem chartGram_pieceSol_closed (hmet : IsMetricCompatible cov) (C : GeodesicCover cov γ a b)
    (htor : cov.torsion = 0) {k : ℕ} (hk : k < C.N) (v : E) :
    ∀ t₁ ∈ Icc (C.c k) (C.c (k + 1)), ∀ t₂ ∈ Icc (C.c k) (C.c (k + 1)),
      Submission.ChartConnection.chartGram (I := I) (C.x k) (γ t₁)
          (pieceSol htor C k v t₁) (pieceSol htor C k v t₁)
        = Submission.ChartConnection.chartGram (I := I) (C.x k) (γ t₂)
            (pieceSol htor C k v t₂) (pieceSol htor C k v t₂) := by
  obtain ⟨t₀, ht₀⟩ := Set.nonempty_Ioo.mpr (C.mono k hk)
  have hmono : C.c k ≠ C.c (k + 1) := (C.mono k hk).ne
  have hcont : ContinuousOn
      (fun t : ℝ => Submission.ChartConnection.chartGram (I := I) (C.x k) (γ t)
        (pieceSol htor C k v t) (pieceSol htor C k v t))
      (Icc (C.c k) (C.c (k + 1))) := by
    refine Submission.BonnetMyers.continuousOn_chartGram_curve (I := I) ?_ ?_ ?_ ?_
    · exact continuousOn_gamma_piece (cov := cov) C hk
    · exact fun t ht =>
        (pieceSol_ode (cov := cov) htor C hk v t ht).continuousAt.continuousWithinAt
    · exact fun t ht =>
        (pieceSol_ode (cov := cov) htor C hk v t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact C.src k hk t (piece_subset_room (cov := cov) C hk ht)
  have hEq : Set.EqOn
      (fun t : ℝ => Submission.ChartConnection.chartGram (I := I) (C.x k) (γ t)
        (pieceSol htor C k v t) (pieceSol htor C k v t))
      (fun _ => Submission.ChartConnection.chartGram (I := I) (C.x k) (γ t₀)
        (pieceSol htor C k v t₀) (pieceSol htor C k v t₀))
      (Icc (C.c k) (C.c (k + 1))) :=
    Set.EqOn.of_subset_closure
      (s := Ioo (C.c k) (C.c (k + 1))) (t := Icc (C.c k) (C.c (k + 1)))
      (fun t ht => chartGram_pieceSol_open (cov := cov) htor hmet C hk v t ht t₀ ht₀)
      hcont continuousOn_const Ioo_subset_Icc_self
      (fun t ht => by rw [closure_Ioo hmono]; exact ht)
  intro t₁ ht₁ t₂ ht₂
  have h1 := hEq ht₁
  have h2 := hEq ht₂
  simp only [] at h1 h2
  rw [h1, h2]

/-! ## §8 The transport is an isometry (global) and is linear in the datum -/

/-- `chartGram x₀ p a a` is the square of the norm of `frameVector x₀ p a`. -/
theorem chartGram_self_eq_norm_sq (x₀ p : M) (a : E) :
    Submission.ChartConnection.chartGram (I := I) x₀ p a a
      = ‖frameVector (I := I) x₀ p a‖ ^ 2 := by
  rw [Submission.ChartConnection.chartGram_apply, real_inner_self_eq_norm_sq]

/-- The Gram value of the datum of piece `k`. -/
theorem gram_datumAt_succ (hmet : IsMetricCompatible cov) (C : GeodesicCover cov γ a b)
    (htor : cov.torsion = 0) (v₀ : E) {k : ℕ} (hk : k + 1 < C.N) :
    Submission.ChartConnection.chartGram (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
        (datumAt htor C v₀ (k + 1)) (datumAt htor C v₀ (k + 1))
      = Submission.ChartConnection.chartGram (I := I) (C.x k) (γ (C.c k))
          (datumAt htor C v₀ k) (datumAt htor C v₀ k) := by
  have hklt : k < C.N := lt_trans (Nat.lt_succ_self k) hk
  have hsrc : γ (C.c (k + 1)) ∈ (chartAt H (C.x (k + 1))).source :=
    C.src (k + 1) hk (C.c (k + 1))
      (piece_subset_room (cov := cov) C hk ⟨le_rfl, (C.mono (k + 1) hk).le⟩)
  have hframe : pieceField (cov := cov) htor C k (datumAt htor C v₀ k) (C.c (k + 1))
      = frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
          (datumAt htor C v₀ (k + 1)) := by
    rw [datumAt_succ]
    exact (Submission.JacobiCoords.frameVector_chartCoords (I := I) hsrc).symm
  have h1 : Submission.ChartConnection.chartGram (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
        (datumAt htor C v₀ (k + 1)) (datumAt htor C v₀ (k + 1))
      = ‖pieceField (cov := cov) htor C k (datumAt htor C v₀ k) (C.c (k + 1))‖ ^ 2 := by
    rw [Submission.ChartConnection.chartGram_apply, ← hframe, real_inner_self_eq_norm_sq]
  have h2 : ‖pieceField (cov := cov) htor C k (datumAt htor C v₀ k) (C.c (k + 1))‖ ^ 2
      = Submission.ChartConnection.chartGram (I := I) (C.x k) (γ (C.c (k + 1)))
          (pieceSol htor C k (datumAt htor C v₀ k) (C.c (k + 1)))
          (pieceSol htor C k (datumAt htor C v₀ k) (C.c (k + 1))) := by
    show ‖frameVector (I := I) (C.x k) (γ (C.c (k + 1)))
        (pieceSol htor C k (datumAt htor C v₀ k) (C.c (k + 1)))‖ ^ 2 = _
    rw [Submission.ChartConnection.chartGram_apply, real_inner_self_eq_norm_sq]
  have h3 : Submission.ChartConnection.chartGram (I := I) (C.x k) (γ (C.c (k + 1)))
        (pieceSol htor C k (datumAt htor C v₀ k) (C.c (k + 1)))
        (pieceSol htor C k (datumAt htor C v₀ k) (C.c (k + 1)))
      = Submission.ChartConnection.chartGram (I := I) (C.x k) (γ (C.c k))
          (datumAt htor C v₀ k) (datumAt htor C v₀ k) := by
    rw [chartGram_pieceSol_closed (cov := cov) hmet C htor hklt (datumAt htor C v₀ k)
      (C.c (k + 1)) ⟨(C.mono k hklt).le, le_rfl⟩ (C.c k) ⟨le_rfl, (C.mono k hklt).le⟩,
      pieceSol_datum (cov := cov) htor C hklt (datumAt htor C v₀ k)]
  rw [h1, h2, h3]

/-- The Gram value of the datum of piece `k` is independent of `k`. -/
theorem gram_datumAt (hmet : IsMetricCompatible cov) (C : GeodesicCover cov γ a b)
    (htor : cov.torsion = 0) (v₀ : E) :
    ∀ k < C.N,
      Submission.ChartConnection.chartGram (I := I) (C.x k) (γ (C.c k))
          (datumAt htor C v₀ k) (datumAt htor C v₀ k)
        = Submission.ChartConnection.chartGram (I := I) (C.x 0) (γ (C.c 0)) v₀ v₀ := by
  intro k
  induction k with
  | zero => intro _; rw [datumAt_zero]
  | succ k ih =>
      intro hk
      rw [gram_datumAt_succ (cov := cov) hmet C htor v₀ hk,
        ih (lt_trans (Nat.lt_succ_self k) hk)]

/-- The piece index of a point of `[c 0, c N]` is a valid piece. -/
theorem kOf_lt (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (t : ℝ) :
    kOf (cov := cov) C hN t < C.N := by
  have h := kOf_le (cov := cov) C hN t
  omega

/-- The point of `[c 0, c N]` lies in its piece. -/
theorem c_kOf_le (C : GeodesicCover cov γ a b) (hN : 0 < C.N) {t : ℝ}
    (ht : t ∈ Icc (C.c 0) (C.c C.N)) :
    C.c (kOf (cov := cov) C hN t) ≤ t := by
  have htb : t ≤ C.c C.N := ht.2
  rcases Nat.eq_zero_or_pos (kOf (cov := cov) C hN t) with h0 | hpos
  · rw [h0]; exact ht.1
  · have hm1 : kOf (cov := cov) C hN t - 1 < kOf (cov := cov) C hN t :=
      Nat.sub_lt hpos Nat.one_pos
    have hnot := kOf_min (cov := cov) C hN t hm1
    rw [Nat.sub_add_cancel hpos, min_eq_left htb] at hnot
    exact le_of_lt (not_le.mp hnot)

/-- The Gram form of the piece-`k` field is the square of the norm of the datum. -/
theorem pieceField_gram (hmet : IsMetricCompatible cov) (C : GeodesicCover cov γ a b)
    (htor : cov.torsion = 0) (v₀ : E) {k : ℕ} (hk : k < C.N) {t : ℝ}
    (ht : t ∈ Icc (C.c k) (C.c (k + 1))) :
    ‖pieceField (cov := cov) htor C k (datumAt htor C v₀ k) t‖ ^ 2
      = ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) v₀‖ ^ 2 := by
  have hkey : Submission.ChartConnection.chartGram (I := I) (C.x k) (γ t)
        (pieceSol htor C k (datumAt htor C v₀ k) t)
        (pieceSol htor C k (datumAt htor C v₀ k) t)
      = ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) v₀‖ ^ 2 := by
    rw [chartGram_pieceSol_closed (cov := cov) hmet C htor hk (datumAt htor C v₀ k) t ht
        (C.c k) ⟨le_rfl, (C.mono k hk).le⟩,
      pieceSol_datum (cov := cov) htor C hk (datumAt htor C v₀ k),
      gram_datumAt (cov := cov) hmet C htor v₀ k hk, chartGram_self_eq_norm_sq]
  rw [← hkey, Submission.ChartConnection.chartGram_apply, real_inner_self_eq_norm_sq]
  simp only [pieceField]

/-- **The transport is an isometry**: the norm of the global parallel field is constant. -/
theorem norm_parallelField_sq (hmet : IsMetricCompatible cov) (C : GeodesicCover cov γ a b)
    (htor : cov.torsion = 0) (hN : 0 < C.N) (v₀ : E) {t : ℝ}
    (ht : t ∈ Icc (C.c 0) (C.c C.N)) :
    ‖parallelField htor C hN v₀ t‖ ^ 2
      = ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) v₀‖ ^ 2 := by
  have htb : t ≤ C.c C.N := ht.2
  show ‖pieceField (cov := cov) htor C (kOf (cov := cov) C hN t)
      (datumAt htor C v₀ (kOf (cov := cov) C hN t)) t‖ ^ 2 = _
  exact pieceField_gram (cov := cov) hmet C htor v₀ (kOf_lt (cov := cov) C hN t)
    ⟨c_kOf_le (cov := cov) C hN ht, kOf_spec' (cov := cov) C hN htb⟩

/-- The norm version of the isometry statement. -/
theorem norm_parallelField (hmet : IsMetricCompatible cov) (C : GeodesicCover cov γ a b)
    (htor : cov.torsion = 0) (hN : 0 < C.N) (v₀ : E) {t : ℝ}
    (ht : t ∈ Icc (C.c 0) (C.c C.N)) :
    ‖parallelField htor C hN v₀ t‖
      = ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) v₀‖ := by
  have hsq := norm_parallelField_sq (cov := cov) hmet C htor hN v₀ ht
  have h := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-- The chart coordinates are additive in the field (pointwise). -/
theorem chartCoords_add_apply {x₀ : M} {J K : (s : ℝ) → TangentSpace I (γ s)} (t : ℝ) :
    Submission.JacobiCoords.chartCoords (I := I) x₀ γ (fun s => J s + K s) t
      = Submission.JacobiCoords.chartCoords (I := I) x₀ γ J t
        + Submission.JacobiCoords.chartCoords (I := I) x₀ γ K t := by
  show (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (J t + K t)
      = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (J t)
        + (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (K t)
  exact map_add _ _ _

/-- The chart coordinates are homogeneous in the field (pointwise). -/
theorem chartCoords_smul_apply {x₀ : M} {J : (s : ℝ) → TangentSpace I (γ s)} (t : ℝ) (c : ℝ) :
    Submission.JacobiCoords.chartCoords (I := I) x₀ γ (fun s => c • J s) t
      = c • Submission.JacobiCoords.chartCoords (I := I) x₀ γ J t := by
  show (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (c • J t)
      = c • (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (J t)
  exact map_smul _ _ _

/-- The piece field is additive in the datum. -/
theorem pieceField_add (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0) {k : ℕ}
    (hk : k < C.N) (v w : E) {t : ℝ} (ht : t ∈ Icc (C.c k) (C.c (k + 1))) :
    pieceField (cov := cov) htor C k (v + w) t
      = pieceField (cov := cov) htor C k v t + pieceField (cov := cov) htor C k w t := by
  show frameVector (I := I) (C.x k) (γ t) (pieceSol htor C k (v + w) t)
      = frameVector (I := I) (C.x k) (γ t) (pieceSol htor C k v t)
        + frameVector (I := I) (C.x k) (γ t) (pieceSol htor C k w t)
  have h := pieceSol_add (cov := cov) htor C hk v w (x := t) ht
  rw [← h, frameVector_add]

/-- The piece field is homogeneous in the datum. -/
theorem pieceField_smul (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0) {k : ℕ}
    (hk : k < C.N) (c : ℝ) (v : E) {t : ℝ} (ht : t ∈ Icc (C.c k) (C.c (k + 1))) :
    pieceField (cov := cov) htor C k (c • v) t
      = c • pieceField (cov := cov) htor C k v t := by
  show frameVector (I := I) (C.x k) (γ t) (pieceSol htor C k (c • v) t)
      = c • frameVector (I := I) (C.x k) (γ t) (pieceSol htor C k v t)
  have h := pieceSol_smul (cov := cov) htor C hk c v (x := t) ht
  rw [← h, frameVector_smul]

/-- The datum recursion is additive. -/
theorem nextDatum_add (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0) {k : ℕ}
    (hk : k < C.N) (v w : E) :
    nextDatum (cov := cov) htor C k (v + w)
      = nextDatum (cov := cov) htor C k v + nextDatum (cov := cov) htor C k w := by
  have hsw : pieceField (cov := cov) htor C k (v + w) (C.c (k + 1))
      = pieceField (cov := cov) htor C k v (C.c (k + 1))
        + pieceField (cov := cov) htor C k w (C.c (k + 1)) :=
    pieceField_add (cov := cov) C htor hk v w ⟨(C.mono k hk).le, le_rfl⟩
  show (trivializationAt E (TangentSpace I) (C.x (k + 1))).continuousLinearMapAt ℝ
        (γ (C.c (k + 1))) (pieceField (cov := cov) htor C k (v + w) (C.c (k + 1)))
      = (trivializationAt E (TangentSpace I) (C.x (k + 1))).continuousLinearMapAt ℝ
          (γ (C.c (k + 1))) (pieceField (cov := cov) htor C k v (C.c (k + 1)))
        + (trivializationAt E (TangentSpace I) (C.x (k + 1))).continuousLinearMapAt ℝ
            (γ (C.c (k + 1))) (pieceField (cov := cov) htor C k w (C.c (k + 1)))
  rw [hsw, map_add]

/-- The datum recursion is homogeneous. -/
theorem nextDatum_smul (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0) {k : ℕ}
    (hk : k < C.N) (c : ℝ) (v : E) :
    nextDatum (cov := cov) htor C k (c • v)
      = c • nextDatum (cov := cov) htor C k v := by
  have hsw : pieceField (cov := cov) htor C k (c • v) (C.c (k + 1))
      = c • pieceField (cov := cov) htor C k v (C.c (k + 1)) :=
    pieceField_smul (cov := cov) C htor hk c v ⟨(C.mono k hk).le, le_rfl⟩
  show (trivializationAt E (TangentSpace I) (C.x (k + 1))).continuousLinearMapAt ℝ
        (γ (C.c (k + 1))) (pieceField (cov := cov) htor C k (c • v) (C.c (k + 1)))
      = c • (trivializationAt E (TangentSpace I) (C.x (k + 1))).continuousLinearMapAt ℝ
            (γ (C.c (k + 1))) (pieceField (cov := cov) htor C k v (C.c (k + 1)))
  rw [hsw, map_smul]

/-- The datum of every piece depends additively on the initial datum. -/
theorem datumAt_add (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0) {v₀ w₀ : E} :
    ∀ k < C.N,
      datumAt htor C (v₀ + w₀) k = datumAt htor C v₀ k + datumAt htor C w₀ k := by
  intro k
  induction k with
  | zero => intro _; rw [datumAt_zero, datumAt_zero, datumAt_zero]
  | succ k ih =>
      intro hk
      have hk' : k < C.N := lt_trans (Nat.lt_succ_self k) hk
      rw [datumAt_succ, datumAt_succ, datumAt_succ, ih hk', nextDatum_add (cov := cov) C htor hk']

/-- The datum of every piece depends homogeneously on the initial datum. -/
theorem datumAt_smul (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0) (c : ℝ) (v₀ : E) :
    ∀ k < C.N, datumAt htor C (c • v₀) k = c • datumAt htor C v₀ k := by
  intro k
  induction k with
  | zero => intro _; rw [datumAt_zero, datumAt_zero]
  | succ k ih =>
      intro hk
      have hk' : k < C.N := lt_trans (Nat.lt_succ_self k) hk
      rw [datumAt_succ, datumAt_succ, ih hk', nextDatum_smul (cov := cov) C htor hk']

/-- **The global parallel field is additive in the datum.** -/
theorem parallelField_add (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0)
    (hN : 0 < C.N) (v₀ w₀ : E) {t : ℝ} (ht : t ∈ Icc (C.c 0) (C.c C.N)) :
    parallelField htor C hN (v₀ + w₀) t
      = parallelField htor C hN v₀ t + parallelField htor C hN w₀ t := by
  have hklt := kOf_lt (cov := cov) C hN t
  have hmem : t ∈ Icc (C.c (kOf (cov := cov) C hN t)) (C.c (kOf (cov := cov) C hN t + 1)) :=
    ⟨c_kOf_le (cov := cov) C hN ht, kOf_spec' (cov := cov) C hN ht.2⟩
  show pieceField (cov := cov) htor C (kOf (cov := cov) C hN t)
        (datumAt htor C (v₀ + w₀) (kOf (cov := cov) C hN t)) t
      = pieceField (cov := cov) htor C (kOf (cov := cov) C hN t)
          (datumAt htor C v₀ (kOf (cov := cov) C hN t)) t
        + pieceField (cov := cov) htor C (kOf (cov := cov) C hN t)
            (datumAt htor C w₀ (kOf (cov := cov) C hN t)) t
  rw [datumAt_add (cov := cov) C htor (kOf (cov := cov) C hN t) hklt,
    pieceField_add (cov := cov) C htor hklt _ _ hmem]

/-- **The global parallel field is homogeneous in the datum.** -/
theorem parallelField_smul (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0)
    (hN : 0 < C.N) (c : ℝ) (v₀ : E) {t : ℝ} (ht : t ∈ Icc (C.c 0) (C.c C.N)) :
    parallelField htor C hN (c • v₀) t = c • parallelField htor C hN v₀ t := by
  have hklt := kOf_lt (cov := cov) C hN t
  have hmem : t ∈ Icc (C.c (kOf (cov := cov) C hN t)) (C.c (kOf (cov := cov) C hN t + 1)) :=
    ⟨c_kOf_le (cov := cov) C hN ht, kOf_spec' (cov := cov) C hN ht.2⟩
  show pieceField (cov := cov) htor C (kOf (cov := cov) C hN t)
        (datumAt htor C (c • v₀) (kOf (cov := cov) C hN t)) t
      = c • pieceField (cov := cov) htor C (kOf (cov := cov) C hN t)
            (datumAt htor C v₀ (kOf (cov := cov) C hN t)) t
  rw [datumAt_smul (cov := cov) C htor c v₀ (kOf (cov := cov) C hN t) hklt,
    pieceField_smul (cov := cov) C htor hklt c _ hmem]


/-- The chart geodesic spray is `-Γ(y)(v,v)`, which is the right-hand side of the *parallel*
equation for the chart velocity `v`. -/
theorem chartGeodesicVectorField_eq_neg_gammaOp {x₀ : M} {u w : ℝ → E} {t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source) :
    chartGeodesicVectorField cov x₀ (u t, w t)
      = -(gammaOp (cov := cov) x₀ u w t (w t)) := by
  rw [chartGeodesicVectorField, gammaOp, christoffelLM_apply (cov := cov) hsrc]

/-- **The chart velocity of a geodesic is parallel along it** (on one piece): the geodesic field
satisfies the parallel equation `y' = -Γ̂ y`.  This is the chart-level form of "a geodesic is
parallel along itself", the fact that makes the holonomy of a closed geodesic preserve the
velocity. -/
theorem pieceSol_deriv (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0) {k : ℕ}
    (hk : k < C.N) :
    EqOn (pieceSol htor C k (deriv (fun s => (extChartAt I (C.x k)) (γ s)) (C.c k)))
      (deriv (fun s => (extChartAt I (C.x k)) (γ s))) (Icc (C.c k) (C.c (k + 1))) := by
  refine (pieceSol_unique (cov := cov) htor C hk
    (deriv (fun s => (extChartAt I (C.x k)) (γ s)) (C.c k)) rfl ?_).symm
  intro t ht
  have hroom : t ∈ Set.Ioo (C.A k) (C.B k) := piece_subset_room (cov := cov) C hk ht
  have hsrc : (extChartAt I (C.x k)).symm
      ((extChartAt I (C.x k)) (γ t)) ∈ (chartAt H (C.x k)).source := by
    have h1 := PartialEquiv.target_subset_preimage_source (extChartAt I (C.x k))
      (chartCoord_mem_target_piece (cov := cov) C hk t ht)
    rwa [extChartAt_source] at h1
  have hcc : coordCurve (I := I) C k = fun s => (extChartAt I (C.x k)) (γ s) := rfl
  rw [hcc]
  refine ((C.ode k hk t hroom).2).congr_deriv ?_
  simp only [chartGeodesicVectorField, gammaOp,
    christoffelLM_apply (cov := cov) hsrc]



/-- **The parallel transport along a geodesic**: the value of the global parallel field with datum
`v` at the right endpoint of the cover. -/
noncomputable def transport (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0)
    (hN : 0 < C.N) (v : E) : TangentSpace I (γ (C.c C.N)) :=
  parallelField (cov := cov) htor C hN v (C.c C.N)

theorem transport_add (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0)
    (hN : 0 < C.N) (v w : E) :
    transport (cov := cov) C htor hN (v + w)
      = transport (cov := cov) C htor hN v + transport (cov := cov) C htor hN w :=
  parallelField_add (cov := cov) C htor hN v w ⟨c_mono_le (cov := cov) C hN.le le_rfl,
    le_rfl⟩

theorem transport_smul (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0)
    (hN : 0 < C.N) (c : ℝ) (v : E) :
    transport (cov := cov) C htor hN (c • v)
      = c • transport (cov := cov) C htor hN v :=
  parallelField_smul (cov := cov) C htor hN c v ⟨c_mono_le (cov := cov) C hN.le le_rfl, le_rfl⟩

theorem transport_norm (hmet : IsMetricCompatible cov) (C : GeodesicCover cov γ a b)
    (htor : cov.torsion = 0) (hN : 0 < C.N) (v : E) :
    ‖transport (cov := cov) C htor hN v‖
      = ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) v‖ :=
  norm_parallelField (cov := cov) hmet C htor hN v ⟨c_mono_le (cov := cov) C hN.le le_rfl, le_rfl⟩

theorem transport_norm_sq (hmet : IsMetricCompatible cov) (C : GeodesicCover cov γ a b)
    (htor : cov.torsion = 0) (hN : 0 < C.N) (v : E) :
    ‖transport (cov := cov) C htor hN v‖ ^ 2
      = ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) v‖ ^ 2 :=
  norm_parallelField_sq (cov := cov) hmet C htor hN v ⟨c_mono_le (cov := cov) C hN.le le_rfl, le_rfl⟩



/-- **The geodesic is differentiable** at every point of a chart room of its cover. -/
theorem mdifferentiableAt_gamma_of_mem_room (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) {t : ℝ} (ht : t ∈ Set.Ioo (C.A k) (C.B k)) :
    MDifferentiableAt 𝓘(ℝ) I γ t := by
  set u : ℝ → E := fun s => (extChartAt I (C.x k)) (γ s) with hu
  have hu' : HasDerivAt u (deriv u t) t := (C.ode k hk t ht).1
  have hdu : ContinuousOn (deriv u) (Set.Ioo (C.A k) (C.B k)) := fun s hs =>
    ((C.ode k hk s hs).2).differentiableAt.continuousAt.continuousWithinAt
  have h1 : ContDiffAt ℝ 1 u t :=
    Commons.Analysis.Calculus.contDiffAt_one_of_hasDerivAt
      (s := Set.Ioo (C.A k) (C.B k)) (isOpen_Ioo.mem_nhds ht)
      (fun y hy => (C.ode k hk y hy).1) hdu
  have h2 : ContMDiffAt 𝓘(ℝ) (modelWithCornersSelf ℝ E) 1 u t :=
    contMDiffAt_iff_contDiffAt.mpr h1
  have hmem : u t ∈ (extChartAt I (C.x k)).target :=
    (extChartAt I (C.x k)).map_source (by
      rw [extChartAt_source]; exact C.src k hk t ht)
  have h3 : ContMDiffAt (modelWithCornersSelf ℝ E) I 1 (extChartAt I (C.x k)).symm (u t) :=
    (contMDiffOn_extChartAt_symm (I := I) (C.x k)).contMDiffAt
      ((isOpen_extChartAt_target (I := I) (C.x k)).mem_nhds hmem)
  have h4 : ContMDiffAt 𝓘(ℝ) I 1 (fun s : ℝ => (extChartAt I (C.x k)).symm (u s)) t :=
    h3.comp t h2
  have hev : γ =ᶠ[𝓝 t] fun s : ℝ => (extChartAt I (C.x k)).symm (u s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (PartialEquiv.left_inv (extChartAt I (C.x k)) (by
      rw [extChartAt_source]; exact C.src k hk s hs)).symm
  exact (h4.congr_of_eventuallyEq hev).mdifferentiableAt (by decide)

/-- **The chart velocity of a geodesic is chart-independent**: it is the intrinsic velocity. -/
theorem frameVector_deriv_coordCurve_eq_curveVelocity (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) {t : ℝ} (ht : t ∈ Set.Ioo (C.A k) (C.B k)) :
    frameVector (I := I) (C.x k) (γ t) (deriv (coordCurve (I := I) C k) t) = curveVelocity (I := I) γ t := by
  refine Submission.ChartIndep.frameVector_chartVel_eq_curveVelocity (I := I)
    (x₀ := C.x k) (u := coordCurve (I := I) C k)
    (w := deriv (coordCurve (I := I) C k)) (C.src k hk t ht) ?_ ?_ ?_ ?_
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (extChartAt I (C.x k)).map_source (by
      rw [extChartAt_source]; exact C.src k hk s hs)
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (PartialEquiv.left_inv (extChartAt I (C.x k)) (by
      rw [extChartAt_source]; exact C.src k hk s hs)).symm
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (C.ode k hk s hs).1
  · exact mdifferentiableAt_gamma_of_mem_room (cov := cov) C hk ht



/-- **The datum of the chart velocity is transported to the chart velocity**: the datum conversion
`nextDatum` maps the chart-`x k` coordinates of the velocity at `c k` to the chart-`x (k+1)`
coordinates of the velocity at `c (k+1)`.  Hence the **velocity field is parallel along the whole
geodesic** and is fixed by the transport `transport`. -/
theorem nextDatum_deriv (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0) {k : ℕ}
    (hk : k + 1 < C.N) :
    nextDatum (cov := cov) htor C k (deriv (fun s => (extChartAt I (C.x k)) (γ s)) (C.c k))
      = deriv (fun s => (extChartAt I (C.x (k + 1))) (γ s)) (C.c (k + 1)) := by
  have hklt : k < C.N := lt_trans (Nat.lt_succ_self k) hk
  have hroomk : C.c (k + 1) ∈ Set.Ioo (C.A k) (C.B k) :=
    piece_subset_room (cov := cov) C hklt ⟨(C.mono k hklt).le, le_rfl⟩
  have hroomk1 : C.c (k + 1) ∈ Set.Ioo (C.A (k + 1)) (C.B (k + 1)) :=
    piece_subset_room (cov := cov) C hk ⟨le_rfl, (C.mono (k + 1) hk).le⟩
  have hsrc : γ (C.c (k + 1)) ∈ (chartAt H (C.x (k + 1))).source :=
    C.src (k + 1) hk (C.c (k + 1)) hroomk1
  have hsol : pieceSol htor C k (deriv (fun s => (extChartAt I (C.x k)) (γ s)) (C.c k))
      (C.c (k + 1)) = deriv (fun s => (extChartAt I (C.x k)) (γ s)) (C.c (k + 1)) :=
    pieceSol_deriv (cov := cov) C htor hklt ⟨(C.mono k hklt).le, le_rfl⟩
  have h1 : frameVector (I := I) (C.x k) (γ (C.c (k + 1)))
      (deriv (fun s => (extChartAt I (C.x k)) (γ s)) (C.c (k + 1)))
      = curveVelocity (I := I) γ (C.c (k + 1)) := by
    have hcc : coordCurve (I := I) C k = fun s => (extChartAt I (C.x k)) (γ s) := rfl
    rw [← hcc]
    exact frameVector_deriv_coordCurve_eq_curveVelocity (cov := cov) C hklt hroomk
  have h2 : curveVelocity (I := I) γ (C.c (k + 1))
      = frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
          (deriv (fun s => (extChartAt I (C.x (k + 1))) (γ s)) (C.c (k + 1))) :=
    (by
      have hcc : coordCurve (I := I) C (k + 1) = fun s => (extChartAt I (C.x (k + 1))) (γ s) := rfl
      rw [← hcc]
      exact (frameVector_deriv_coordCurve_eq_curveVelocity (cov := cov) C hk hroomk1).symm)
  have hkey : pieceField (cov := cov) htor C k
        (deriv (fun s => (extChartAt I (C.x k)) (γ s)) (C.c k)) (C.c (k + 1))
      = frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
          (deriv (fun s => (extChartAt I (C.x (k + 1))) (γ s)) (C.c (k + 1))) := by
    show frameVector (I := I) (C.x k) (γ (C.c (k + 1)))
        (pieceSol htor C k (deriv (fun s => (extChartAt I (C.x k)) (γ s)) (C.c k))
          (C.c (k + 1)))
      = frameVector (I := I) (C.x (k + 1)) (γ (C.c (k + 1)))
          (deriv (fun s => (extChartAt I (C.x (k + 1))) (γ s)) (C.c (k + 1)))
    rw [hsol, h1, h2]
  show (trivializationAt E (TangentSpace I) (C.x (k + 1))).continuousLinearMapAt ℝ
      (γ (C.c (k + 1)))
      (pieceField (cov := cov) htor C k
        (deriv (fun s => (extChartAt I (C.x k)) (γ s)) (C.c k)) (C.c (k + 1)))
    = deriv (fun s => (extChartAt I (C.x (k + 1))) (γ s)) (C.c (k + 1))
  rw [hkey]
  exact Submission.GlobalBM.continuousLinearMapAt_frameVector (I := I) (C.x (k + 1))
    (γ (C.c (k + 1))) hsrc _



/-- **Strict** monotonicity of the partition. -/
theorem c_mono_lt (C : GeodesicCover cov γ a b) {i j : ℕ} (hij : i < j) (hj : j ≤ C.N) :
    C.c i < C.c j := by
  have h1 : C.c i < C.c (i + 1) :=
    C.mono i (lt_of_lt_of_le (Nat.lt_succ_self i) (le_trans (Nat.succ_le_of_lt hij) hj))
  have h2 : C.c (i + 1) ≤ C.c j := c_mono_le (cov := cov) C (Nat.succ_le_of_lt hij) hj
  linarith

/-- The piece index of the right endpoint. -/
theorem kOf_last (C : GeodesicCover cov γ a b) (hN : 0 < C.N) :
    kOf (cov := cov) C hN (C.c C.N) = C.N - 1 := by
  refine le_antisymm (kOf_le (cov := cov) C hN _) ?_
  by_contra hcon
  have h2 : kOf (cov := cov) C hN (C.c C.N) + 1 < C.N := by omega
  have h3 : C.c (kOf (cov := cov) C hN (C.c C.N) + 1) < C.c C.N :=
    c_mono_lt (cov := cov) C h2 le_rfl
  have h4 := kOf_spec (cov := cov) C hN (C.c C.N)
  rw [min_self] at h4
  linarith

/-- **The datum recursion tracks the chart velocity**: the datum of piece `k` is the chart-`x k`
velocity at `c k`. -/
theorem datumAt_deriv (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0) :
    ∀ k < C.N,
      datumAt htor C (deriv (fun s => (extChartAt I (C.x 0)) (γ s)) (C.c 0)) k
        = deriv (fun s => (extChartAt I (C.x k)) (γ s)) (C.c k) := by
  intro k
  induction k with
  | zero => intro _; rw [datumAt_zero]
  | succ k ih =>
      intro hk
      have hklt : k < C.N := lt_trans (Nat.lt_succ_self k) hk
      rw [datumAt_succ, ih hklt, nextDatum_deriv (cov := cov) C htor hk]

/-- **The transport fixes the velocity**: the parallel transport of the chart velocity at the base
time is the intrinsic velocity at the endpoint. -/
theorem transport_velocity (C : GeodesicCover cov γ a b) (htor : cov.torsion = 0)
    (hN : 0 < C.N) :
    transport (cov := cov) C htor hN (deriv (fun s => (extChartAt I (C.x 0)) (γ s)) (C.c 0))
      = curveVelocity (I := I) γ (C.c C.N) := by
  have hlast := kOf_last (cov := cov) C hN
  have hkN : C.N - 1 < C.N := Nat.sub_lt hN Nat.one_pos
  have hlt : C.c (C.N - 1) < C.c C.N := by
    have h := C.mono (C.N - 1) hkN
    rwa [Nat.sub_add_cancel hN] at h
  have hmem : C.c (kOf (cov := cov) C hN (C.c C.N)) < C.c C.N := by
    rw [hlast]; exact hlt
  have hpiece := parallelField_piece (cov := cov) htor C hN
    (deriv (fun s => (extChartAt I (C.x 0)) (γ s)) (C.c 0))
    (kOf_lt (cov := cov) C hN (C.c C.N)) hmem
    (by rw [hlast, Nat.sub_add_cancel hN])
  rw [transport, hpiece, hlast]
  show frameVector (I := I) (C.x (C.N - 1)) (γ (C.c C.N))
      (pieceSol htor C (C.N - 1)
        (datumAt htor C (deriv (fun s => (extChartAt I (C.x 0)) (γ s)) (C.c 0)) (C.N - 1))
        (C.c C.N)) = curveVelocity (I := I) γ (C.c C.N)
  rw [datumAt_deriv (cov := cov) C htor (C.N - 1) hkN,
    pieceSol_deriv (cov := cov) C htor hkN ⟨hlt.le, by rw [Nat.sub_add_cancel hN]⟩]
  exact frameVector_deriv_coordCurve_eq_curveVelocity (cov := cov) C hkN
    (piece_subset_room (cov := cov) C hkN ⟨hlt.le, by rw [Nat.sub_add_cancel hN]⟩)


end
end Submission.ParallelGlobal
