import Submission.Work.SignatureBordism.exists_ball_manifold

set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary of the closed ball: `∂D^{n+1} = S^n`

`Submission/Work/SignatureBordism/exists_ball_manifold.lean` equips the closed unit ball
`Ball n = D^{n+1} ⊆ ℝ^{n+1}` with a `ChartedSpace` structure over the half-space
`Half n = EuclideanHalfSpace (n+1)` making it a smooth manifold with boundary.  This file

* registers that structure as instances (`instChartedSpaceBall`, `instIsManifoldBall`) so that the
  ball can be used as a bordism in `Submission/Work/SignatureBordism/BordismRelation.lean`;
* identifies the **boundary**: `Work.SignatureBordism.ball_boundary`,
  `(hModel n).boundary (Ball n) = ballSphere n`, the sphere inside the ball — the boundary points of
  the disc are exactly the unit vectors.  The computation is by inspection of the (explicit)
  preferred chart `ballChartAt`: at a point of the source of the centre chart `interiorChart`, the
  first coordinate of the chart is `max (x₀ + 1/2) 0 = x₀ + 1/2 > 0` (so the point is interior);
  otherwise the preferred chart is a half-ball chart `halfChart n i b`, whose first coordinate is
  `1 - ‖x‖`, which vanishes exactly on the unit sphere;
* sets up the objects of the disc bordism: the sphere as a subset of the ball (`ballSphere`), the
  disc as a topological space (`disc`) with its boundary subset (`discBoundary`), and the unit
  sphere as a closed smooth manifold (`endSphere`) — the *end* of the bordism whose middle-form
  data is built in `Submission/Work/SignatureBordism/DiscBordism.lean`;
* the inclusion `sphereToBall` of the unit sphere into the ball, whose smoothness
  (`Work.SignatureBordism.ball_smoothSphere`) is the single geometric input of the disc bordism.

## Conventions

Everything is stated for the *specific* closed ball `Ball n`, with the `ChartedSpace` structure of
`Work.SignatureBordism.ballChartedSpace n`; the model with corners is `hModel n`, i.e. the
half-space model `𝓡∂ (n+1)`.
-/

open scoped Manifold ContDiff Topology
open Metric WithLp
open Classical

set_option maxHeartbeats 1600000

namespace Work.SignatureBordism

noncomputable section

/-! ## The ball as a smooth manifold with boundary -/

/-- The charted space structure of `exists_ball_manifold`, as a global instance. -/
instance instChartedSpaceBall (n : ℕ) : ChartedSpace (Half n) (Ball n) := ballChartedSpace n

/-- **The closed ball is a smooth manifold with boundary** in the half-space model. -/
instance instIsManifoldBall (n : ℕ) : IsManifold (hModel n) ∞ (Ball n) :=
  haveI : IsManifold (hModel n) (⊤ : WithTop ℕ∞) (Ball n) := ball_isManifold n
  IsManifold.of_le (m := ∞) (n := (⊤ : WithTop ℕ∞)) le_top

/-- The closed ball is compact. -/
instance instCompactSpaceBall (n : ℕ) : CompactSpace (Ball n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The unit sphere `S^n`, as a subset of the closed ball `D^{n+1}`. -/
def ballSphere (n : ℕ) : Set (Ball n) :=
  {x | (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}

lemma mem_ballSphere_iff (n : ℕ) (x : Ball n) :
    x ∈ ballSphere n ↔
      (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  Iff.rfl

lemma mem_ballSphere_iff_norm (n : ℕ) (x : Ball n) :
    x ∈ ballSphere n ↔ ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
  rw [mem_ballSphere_iff, Metric.mem_sphere, dist_eq_norm, sub_zero]

/-! ## The computation of the boundary -/

/-- The extended chart of the ball is the model map applied to the preferred chart. -/
lemma extChartAt_ball (n : ℕ) (x : Ball n) :
    extChartAt (hModel n) x x = ((chartAt (Half n) x) x : Half n).val := rfl

/-- **The boundary points of the disc are the unit vectors.** -/
theorem ball_mem_boundary_iff_norm (n : ℕ) (x : Ball n) :
    x ∈ (hModel n).boundary (Ball n) ↔ ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
  have hfront : frontier (Set.range (hModel n)) =
      {y : EuclideanSpace ℝ (Fin (n + 1)) | 0 = y 0} :=
    frontier_range_modelWithCornersEuclideanHalfSpace (n + 1)
  rw [ModelWithCorners.boundary, Set.mem_ofPred_eq, ModelWithCorners.isBoundaryPoint_iff, hfront,
    Set.mem_ofPred_eq, extChartAt_ball]
  by_cases hmem : x ∈ interiorSource n
  · have hc : chartAt (Half n) x = interiorChart n := ballChartAt_of_mem n hmem
    have h1 : -(1 / 2 : ℝ) < (x : EuclideanSpace ℝ (Fin (n + 1))) 0 := hmem.1
    have h2 : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1 := hmem.2
    rw [hc, interiorChart_apply, interiorToFunE_coord, max_eq_left (show (0 : ℝ) ≤
      (x : EuclideanSpace ℝ (Fin (n + 1))) 0 + 1 / 2 by linarith)]
    constructor
    · intro h
      linarith
    · intro h
      rw [h] at h2
      exact absurd h2 (lt_irrefl 1)
  · have hc : chartAt (Half n) x = ballHalfChartAt n x hmem := ballChartAt_of_not_mem n hmem
    rw [hc, ballHalfChartAt, halfChart_apply, halfToFunE_zero]
    constructor <;> intro h <;> linarith

/-- **The boundary of the closed disc `D^{n+1}` is the unit sphere `S^n`.** -/
theorem ball_boundary (n : ℕ) : (hModel n).boundary (Ball n) = ballSphere n := by
  ext x
  rw [ball_mem_boundary_iff_norm n x, mem_ballSphere_iff_norm]

/-- A boundary point of the ball is not in the source of the centre chart (its norm is `1`). -/
lemma not_mem_interiorSource_of_mem_boundary (n : ℕ) {x : Ball n}
    (hx : x ∈ (hModel n).boundary (Ball n)) : x ∉ interiorSource n := by
  intro h
  rw [ball_mem_boundary_iff_norm n x] at hx
  exact absurd hx (ne_of_lt h.2)

/-- A boundary point of the ball is non-zero. -/
lemma ne_zero_of_mem_boundary (n : ℕ) {x : Ball n} (hx : x ∈ (hModel n).boundary (Ball n)) :
    (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
  intro h
  rw [ball_mem_boundary_iff_norm n x, h, norm_zero] at hx
  exact one_ne_zero hx.symm

/-! ## The sphere as the boundary end of the disc -/

/-- The unit sphere `S^n ⊆ D^{n+1}`, as a (closed smooth) manifold: the *end* of the disc bordism.

The manifold structure is Mathlib's (`Geometry/Manifold/Instances/Sphere.lean`): the sphere is
charted on `EuclideanSpace ℝ (Fin n)` by stereographic projection, and is an analytic (hence
smooth) manifold. -/
abbrev endSphere (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The inclusion of the unit sphere into the closed ball: the inclusion of the *boundary* of the
disc. -/
def sphereToBall (n : ℕ) : endSphere n → Ball n :=
  fun x => ⟨(x : EuclideanSpace ℝ (Fin (n + 1))), by
    have hx : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using x.2
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq hx⟩

@[simp] lemma sphereToBall_coe (n : ℕ) (x : endSphere n) :
    ((sphereToBall n x : Ball n) : EuclideanSpace ℝ (Fin (n + 1)))
      = (x : EuclideanSpace ℝ (Fin (n + 1))) := rfl

lemma sphereToBall_mem_ballSphere (n : ℕ) (x : endSphere n) :
    sphereToBall n x ∈ ballSphere n := by
  rw [mem_ballSphere_iff, sphereToBall_coe]
  exact x.2

/-- The inclusion of the unit sphere into the ball is continuous. -/
lemma continuous_sphereToBall (n : ℕ) : Continuous (sphereToBall n) :=
  Continuous.subtype_mk (f := fun x : endSphere n => (x : EuclideanSpace ℝ (Fin (n + 1))))
    continuous_subtype_val (fun x => (sphereToBall n x).property)

/-- **The sphere `S^n` is homeomorphic to the boundary of the disc `D^{n+1}`** (the sphere regarded
as a subset of the ball). -/
noncomputable def ballBoundaryHomeo (n : ℕ) : endSphere n ≃ₜ ↥(ballSphere n) where
  toFun := fun x => ⟨sphereToBall n x, sphereToBall_mem_ballSphere n x⟩
  invFun := fun y => ⟨(y : Ball n), (mem_ballSphere_iff (n := n) (x := (y : Ball n))).mp y.2⟩
  left_inv := fun x => Subtype.ext rfl
  right_inv := fun y => Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk (continuous_sphereToBall n)
    (fun x => sphereToBall_mem_ballSphere n x)
  continuous_invFun := Continuous.subtype_mk
    (f := fun y : ↥(ballSphere n) => (y : EuclideanSpace ℝ (Fin (n + 1))))
    (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)

/-! ## The disc as a topological space -/

/-- The disc `D^{2k+1}` (the closed ball in `ℝ^{2k+2}`), as a topological space: the underlying
space of the bordism `W` of the disc. -/
abbrev disc (k : ℕ) : TopCat := TopCat.of (Ball (k + k))

/-- The boundary `S^{2k}` of the disc, as a subset of the disc. -/
def discBoundary (k : ℕ) : Set (disc k) := ballSphere (k + k)

lemma mem_discBoundary_iff (k : ℕ) (x : disc k) :
    x ∈ discBoundary k ↔ ‖(x : EuclideanSpace ℝ (Fin (k + k + 1)))‖ = 1 :=
  mem_ballSphere_iff_norm (k + k) x

end

end Work.SignatureBordism
