import Mathlib
import Submission.Work.Drive.Morse

/-!
# The local model of a regular level set of a smooth function on a surface

This file fixes the vocabulary for `Work.Drive.N2.regularLevelCircles`: the model spaces of the
level set (a `1`-manifold) and of the surface, and the local "graph" description of the level set
in an ambient chart, which is the input of the construction of the smooth structure on the level
set.

The level set of `f` over `t` is `{x | f x = t}`; at a point `y` of it which is not critical, the
chart at `y` identifies a neighbourhood of `y` with an open subset of `ℝ²`, and the level set there
is the graph `{η s | s ∈ T}` of a smooth function over one coordinate axis.  `LevelModel` records
that data.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

noncomputable section

/-- The model space of the level set (a `1`-manifold). -/
abbrev E1 : Type := EuclideanSpace ℝ (Fin 1)

/-- The model space of the surface. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The model with corners of the level set. -/
abbrev I1 : ModelWithCorners ℝ E1 E1 := modelWithCornersSelf ℝ E1

/-- The smoothness index `C^∞`. -/
abbrev sm : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The level set `f ⁻¹' {t}`, as a type. -/
abbrev LevelSet {M : Type*} (f : M → ℝ) (t : ℝ) := {x : M // f x = t}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E2 M]

/-- **The local model of a regular level set.**  At a point `y` of the level set of `f` over `t`,
the level set is, in the chart at `y`, locally the graph of a smooth function of one of the two
coordinates; this structure records that data.

The two coordinates of the chart at `y` are indexed by `Fin 2`; `i` is the coordinate which is
*kept* by the chart of the level set, so that on the graph the coordinate `i` runs over the
interval `T` and the parametrisation is `s ↦ η s` (`s` being the coordinate `i`). -/
structure LevelModel (f : M → ℝ) (t : ℝ) (y : LevelSet f t) where
  /-- the coordinate of the ambient chart which the level set charts onto -/
  i : Fin 2
  /-- a neighbourhood of the chart point of `y` on which the graph description holds -/
  V : Set E2
  /-- `V` is open -/
  isOpen_V : IsOpen V
  /-- the graph parametrisation, in the chart at `y` -/
  η : ℝ → E2
  /-- the interval of coordinates covered by the parametrisation -/
  T : Set ℝ
  /-- `T` is open -/
  isOpen_T : IsOpen T
  /-- the `i`-coordinate of the chart point of `y` lies in `T` -/
  base_mem_T : ((chartAt E2 y.1) y.1).ofLp i ∈ T
  /-- the parametrisation is smooth -/
  contDiffOn_η : ContDiffOn ℝ ∞ η T
  /-- the parametrisation passes through the chart point of `y` -/
  base_eq : η (((chartAt E2 y.1) y.1).ofLp i) = (chartAt E2 y.1) y.1
  /-- the graph lies in `V` -/
  mem_V : ∀ s ∈ T, η s ∈ V
  /-- the graph lies in the chart's target -/
  mem_target : ∀ s ∈ T, η s ∈ (chartAt E2 y.1).target
  /-- the parametrisation is a graph over the coordinate `i` -/
  coord : ∀ s ∈ T, (η s).ofLp i = s
  /-- the graph lies on the level set -/
  level : ∀ s ∈ T, f ((chartAt E2 y.1).symm (η s)) = t
  /-- every point of `V` which lies on the level set has its `i`-coordinate in `T` -/
  mem_T : ∀ v ∈ V, f ((chartAt E2 y.1).symm v) = t → v.ofLp i ∈ T
  /-- conversely, near `y` the level set is exactly the graph -/
  graph : ∀ v ∈ V, f ((chartAt E2 y.1).symm v) = t → η (v.ofLp i) = v

end

end Work.Drive.N2
