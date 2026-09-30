import Submission.Work.RiemLib.Rauch
import Submission.Work.RiemLib.ChartBounds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Symmetries of the curvature tensor on tangent vectors

This file adds the remaining *algebraic* symmetries of the Riemann curvature tensor that are needed
by the Jacobi-equation chapter, in the vector form `curvVec`:

* `curvVec_bianchi` : the first Bianchi identity `R(u,v)w + R(v,w)u + R(w,u)v = 0`;
* `inner_curvVec_pair_symm` : the "one-slot" pair symmetry `⟪R(u,v)w, v⟫ = ⟪R(w,v)u, v⟫`;
* `inner_curvVec_self_adjoint` : **self-adjointness of the curvature endomorphism**
  `⟪R(u,v)v, w⟫ = ⟪u, R(w,v)v⟫`;
* `chartCurv_self_adjoint` and `chartCurv_lower_bound_normal`, the same statements in the chart
  coordinates used by the Jacobi equation (`R(σ_X,σ_Y)σ_Y = σ_{chartCurv X Y}`).

Self-adjointness of `v ↦ R(v,w)w` is exactly what makes the coordinate Jacobi equation
`D(Dy) + chartCurv(y,w) = 0` a *linear ODE with self-adjoint coefficients*, hence amenable to the
Riccati comparison behind Rauch's theorem.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Curvature
open Submission.CurvatureVec
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.Rauch
open Submission.Geodesic

namespace Submission.CurvatureSym

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **The first Bianchi identity for `curvVec`**:
`R(u,v)w + R(v,w)u + R(w,u)v = 0`. -/
theorem curvVec_bianchi (hcov : ContMDiffCovariantDerivative cov ∞) (htor : cov.torsion = 0)
    (x : M) (u v w : TangentSpace I x) :
    curvVec cov x u v w + curvVec cov x v w u + curvVec cov x w u v = 0 := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  obtain ⟨Z, hZ, hZx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w
  rw [curvVec_eq cov hcov hX hY hZ hXx hYx hZx,
    curvVec_eq cov hcov hY hZ hX hYx hZx hXx,
    curvVec_eq cov hcov hZ hX hY hZx hXx hYx]
  exact curv_bianchi cov hcov htor hX hY hZ

/-- **Pair symmetry, "one-slot" form**: `⟪R(u,v)w, v⟫ = ⟪R(w,v)u, v⟫`. -/
theorem inner_curvVec_pair_symm (hcov : ContMDiffCovariantDerivative cov ∞)
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (x : M) (u v w : TangentSpace I x) :
    inner ℝ (curvVec cov x u v w) v = inner ℝ (curvVec cov x w v u) v := by
  have hb := curvVec_bianchi (cov := cov) hcov htor x u v w
  have h1 : inner ℝ (curvVec cov x u v w) v
      + inner ℝ (curvVec cov x v w u) v + inner ℝ (curvVec cov x w u v) v = 0 := by
    have h := congrArg (fun z : TangentSpace I x => inner ℝ z v) hb
    simpa only [inner_add_left, inner_zero_left] using h
  -- `⟪R(w,u)v, v⟫ = 0`
  have h2 : inner ℝ (curvVec cov x w u v) v = 0 := by
    have h := inner_curvVec_skew cov hcov hmet x w u v v
    have hcomm : inner ℝ v (curvVec cov x w u v) = inner ℝ (curvVec cov x w u v) v :=
      real_inner_comm _ _
    linarith
  -- `⟪R(v,w)u, v⟫ = -⟪R(w,v)u, v⟫`
  have h3 : inner ℝ (curvVec cov x v w u) v = -inner ℝ (curvVec cov x w v u) v := by
    rw [curvVec_antisymm cov hcov x v w u, inner_neg_left]
  rw [h2, add_zero, h3] at h1
  linarith

/-- **Self-adjointness of the curvature endomorphism `v ↦ R(v,w)w`**:
`⟪R(u,w)w, z⟫ = ⟪u, R(z,w)w⟫`. -/
theorem inner_curvVec_self_adjoint (hcov : ContMDiffCovariantDerivative cov ∞)
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (x : M) (u w z : TangentSpace I x) :
    inner ℝ (curvVec cov x u w w) z = inner ℝ u (curvVec cov x z w w) := by
  have hskew1 : inner ℝ (curvVec cov x u w w) z = -inner ℝ (curvVec cov x u w z) w := by
    have h := inner_curvVec_skew cov hcov hmet x u w w z
    have hcomm : inner ℝ w (curvVec cov x u w z) = inner ℝ (curvVec cov x u w z) w :=
      real_inner_comm _ _
    linarith
  have hpair := inner_curvVec_pair_symm (cov := cov) hcov htor hmet x u w z
  have hskew2 : inner ℝ (curvVec cov x z w w) u = -inner ℝ (curvVec cov x z w u) w := by
    have h := inner_curvVec_skew cov hcov hmet x z w w u
    have hcomm : inner ℝ w (curvVec cov x z w u) = inner ℝ (curvVec cov x z w u) w :=
      real_inner_comm _ _
    linarith
  have hcommZ : inner ℝ (curvVec cov x z w w) u = inner ℝ u (curvVec cov x z w w) :=
    real_inner_comm _ _
  linarith

/-! ## Chart form -/

/-- **Self-adjointness of the chart curvature term**: `chartCurv X Y` is the coordinate vector of
`R(σ_X, σ_Y)σ_Y`, so it is self-adjoint for the chart metric:
`⟨chartCurv X Y, Z⟩ = ⟨X, chartCurv Z Y⟩`. -/
theorem chartCurv_self_adjoint (hcov : ContMDiffCovariantDerivative cov ∞)
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (x₀ : M)
    {p : M} (hp : p ∈ (chartAt H x₀).source) (X Y Z : E) :
    chartGram (I := I) x₀ p (chartCurv cov x₀ p X Y) Z
      = chartGram (I := I) x₀ p X (chartCurv cov x₀ p Z Y) := by
  haveI : ContMDiffCovariantDerivative cov ∞ := hcov
  rw [chartGram_apply, chartGram_apply,
    ← curvVec_frameVector_eq (cov := cov) htor x₀ hp X Y,
    ← curvVec_frameVector_eq (cov := cov) htor x₀ hp Z Y]
  exact inner_curvVec_self_adjoint (cov := cov) hcov htor hmet p
    (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y)
    (frameVector (I := I) x₀ p Z)

/-- **Lower bound for the chart curvature term** in the normal direction: for `Y` of unit chart norm
and `X` orthogonal to it, `chartGram X X ≤ chartGram (chartCurv X Y) X` — the normalised lower
pinching bound `K_min > 1` of `QuarterPinched`, stated with the constant `1`. -/
theorem chartCurv_lower_bound_normal (hcov : ContMDiffCovariantDerivative cov ∞)
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov) (x₀ : M)
    {p : M} (hp : p ∈ (chartAt H x₀).source) {X Y : E}
    (hun : chartGram (I := I) x₀ p Y Y = 1)
    (horth : chartGram (I := I) x₀ p X Y = 0) :
    chartGram (I := I) x₀ p X X ≤ chartGram (I := I) x₀ p (chartCurv cov x₀ p X Y) X := by
  haveI : ContMDiffCovariantDerivative cov ∞ := hcov
  rcases eq_or_ne X 0 with hX0 | hX0
  · subst hX0
    simp
  have hun' : ‖frameVector (I := I) x₀ p Y‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, ← chartGram_apply]
    exact hun
  have horth' : inner ℝ (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y) = 0 := by
    rw [← chartGram_apply]
    exact horth
  have hgram : gramFormVec p (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y)
      = chartGram (I := I) x₀ p X X := by
    rw [gramFormVec, hun', horth', chartGram_apply, real_inner_self_eq_norm_sq]
    ring
  have hG : gramFormVec p (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y) ≠ 0 := by
    rw [hgram]
    exact ne_of_gt (chartGram_self_pos hp hX0)
  have hb := gramFormVec_le_curvFormVec (cov := cov) hcov hmet hpinch p
    (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y) hG
  have hcurv : curvFormVec cov p (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y)
      = chartGram (I := I) x₀ p (chartCurv cov x₀ p X Y) X := by
    rw [← inner_curvVec_self (cov := cov) hcov p (frameVector (I := I) x₀ p X)
      (frameVector (I := I) x₀ p Y)]
    rw [curvVec_frameVector_eq (cov := cov) htor x₀ hp X Y, chartGram_apply]
  rw [hgram, hcurv] at hb
  exact hb

end

end Submission.CurvatureSym
