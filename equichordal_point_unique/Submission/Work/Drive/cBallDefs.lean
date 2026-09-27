import Mathlib

/-!
# Coordinate balls and fine chains on a `ℂ`-charted space

The definitions shared by the construction of `Work.Drive.exists_phase_chain_charts`:

* `cBall c x r` — the points of the source of the chart `c` whose coordinate lies in the open disc of
  radius `r` around the coordinate of `x`;
* `FineChain c x r l` — the consecutive points of the list `l` start at its head and each step is
  smaller than one eighth of the distance from the earlier point's coordinate to the boundary of the
  model disc of radius `r`; this is exactly the amount needed for the `8 ρ`-ball around the earlier
  point to lie in that model disc.
-/

open Set Metric

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The `c`-coordinate ball of radius `r` around `x`. -/
def cBall (c : OpenPartialHomeomorph X ℂ) (x : X) (r : ℝ) : Set X :=
  {z : X | z ∈ c.source ∧ c z ∈ Metric.ball (c x) r}

@[simp] theorem mem_cBall {c : OpenPartialHomeomorph X ℂ} {x z : X} {r : ℝ} :
    z ∈ cBall c x r ↔ z ∈ c.source ∧ c z ∈ Metric.ball (c x) r := Iff.rfl

theorem cBall_subset_source {c : OpenPartialHomeomorph X ℂ} {x : X} {r : ℝ} :
    cBall c x r ⊆ c.source := fun _ hy => hy.1

/-- `FineChain` along a list: consecutive points are close together, measured against the distance
from the earlier coordinate to the boundary of the model disc of radius `r`. -/
def FineChain (c : OpenPartialHomeomorph X ℂ) (x : X) (r : ℝ) : List X → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => dist (c v) (c u) < (r - dist (c u) (c x)) / 8 ∧ FineChain c x r (v :: rest)

/-- If the *closed* model ball of radius `r` lies in the target of `c`, then the closure in `X` of
the `c`-coordinate ball of radius `r` is contained in the source of `c`. -/
theorem closure_cBall_subset_source {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    {c : OpenPartialHomeomorph X ℂ} {x : X} {r : ℝ}
    (hroom : Metric.closedBall (c x) r ⊆ c.target) : closure (cBall c x r) ⊆ c.source := by
  have hsub : cBall c x r ⊆ c.symm '' Metric.closedBall (c x) r := by
    rintro z ⟨hz, hzc⟩
    exact ⟨c z, Metric.ball_subset_closedBall hzc, c.left_inv hz⟩
  have hcomp : IsCompact (c.symm '' Metric.closedBall (c x) r) :=
    (isCompact_closedBall (c x) r).image_of_continuousOn (c.continuousOn_symm.mono hroom)
  have hcl : closure (cBall c x r) ⊆ c.symm '' Metric.closedBall (c x) r :=
    closure_minimal hsub hcomp.isClosed
  rintro z hz
  obtain ⟨w, hw, hwz⟩ := hcl hz
  rw [← hwz]
  exact c.map_target (hroom hw)

/-- A point of the model ball around the centre has room: the model ball of radius `8 ρ` around it
lies in the model ball of radius `r`. -/
theorem ball_eight_subset {c : OpenPartialHomeomorph X ℂ} {x u : X} {r : ℝ}
    (hu : c u ∈ Metric.ball (c x) r) :
    Metric.ball (c u) (8 * ((r - dist (c u) (c x)) / 8)) ⊆ Metric.ball (c x) r := by
  intro w hw
  rw [Metric.mem_ball] at hw ⊢
  have h1 : dist (c u) (c x) < r := hu
  have h3 : 8 * ((r - dist (c u) (c x)) / 8) = r - dist (c u) (c x) := by ring
  rw [h3] at hw
  have h2 : dist w (c x) ≤ dist w (c u) + dist (c u) (c x) := dist_triangle w (c u) (c x)
  linarith


/-- A closed model ball of radius `r - dist (c u) (c x)` around `c u` lies in the closed model ball
of radius `r` around `c x`, as soon as `dist (c u) (c x) < r`. -/
theorem closedBall_room_subset {c : OpenPartialHomeomorph X ℂ} {x u : X} {r : ℝ}
    (hu : dist (c u) (c x) < r) :
    Metric.closedBall (c u) (r - dist (c u) (c x)) ⊆ Metric.closedBall (c x) r := by
  intro w hw
  rw [Metric.mem_closedBall] at hw ⊢
  linarith [dist_triangle w (c u) (c x)]


/-- Membership in the image description of a coordinate ball. -/
theorem mem_image_symm_ball_iff {c : OpenPartialHomeomorph X ℂ} {x z : X} {r : ℝ}
    (hr : Metric.closedBall (c x) r ⊆ c.target) :
    z ∈ c.symm '' Metric.ball (c x) r ↔ z ∈ c.source ∧ c z ∈ Metric.ball (c x) r := by
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hwt : w ∈ c.target := hr (Metric.ball_subset_closedBall hw)
    refine ⟨by rw [← hwz]; exact c.map_target hwt, ?_⟩
    rw [← hwz, c.right_inv hwt]
    exact hw
  · rintro ⟨hz, hzc⟩
    exact ⟨c z, hzc, c.left_inv hz⟩

end Work.Drive
