import ChallengeDeps
import Submission.Bridge.SupLayer
import Submission.GeometryOfNumbers.ProjectionDistance
import Submission.Commons.Analysis.InnerProductSpace.residualSup_eq_of_finrank_eq

/-!
# Bridge, challenge binding

Instantiate the generic bridge (`Submission.Bridge.SupLayer`) to the space
`ℝᵈ = EuclideanSpace ℝ (Fin d)` of the challenge and connect the generic mirrors with the
actual `LinearSubspaces` definitions:

* `LinearSubspaces.distLineSubspace` (min over lines of the subspace of the sine of the angle)
  equals the residual `‖u - π_s u‖` of a unit vector spanning the line;
* for `finrank v < finrank x`, the challenge distance `LinearSubspaces.distSubspaces v x`
  equals `Submission.ProjectionDistance.planeResidual v x` (the maximal orthogonal residual
  over unit vectors of `v`, the `δ(v,x)` of the model work).

The equal-dimension case `finrank v = finrank x` needs the symmetry of the Grassmann metric
(`δ(v,x) = δ(x,v)`), which is recorded separately (see `Submission/Work/ROADMAP.md`).
-/

noncomputable section

open scoped LinearAlgebra.Projectivization
open Module Real InnerProductGeometry Real
open LinearSubspaces

set_option autoImplicit false

namespace Submission.Bridge

variable {d : ℕ}
abbrev RD (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

open Submission.Bridge.Core
open Submission.Bridge.Projective
open Submission.Bridge.SupLayer

/-- The line-to-subspace distance of the challenge is the generic `lineToSubspace`. -/
lemma distLineSubspace_eq_lineToSubspace (X : ℙ ℝ (RD d)) (s : Submodule ℝ (RD d)) :
    LinearSubspaces.distLineSubspace X s = lineToSubspace X s := by
  rfl

/-- `distLineSubspace` of the line spanned by a unit vector equals the orthogonal residual. -/
lemma distLineSubspace_eq_residual (u : RD d) (hu1 : ‖u‖ = 1) (hu : u ≠ 0)
    (s : Submodule ℝ (RD d)) (hs : s ≠ ⊥) :
    LinearSubspaces.distLineSubspace (Projectivization.mk ℝ u hu) s =
      ‖u - s.starProjection u‖ := by
  rw [distLineSubspace_eq_lineToSubspace]
  exact lineToSubspace_mk_unit u hu1 hu s hs

/-- The generic mirror of `distSubspaces` is the challenge's `distSubspaces`. -/
lemma distSubspaces_eq_mirror (x y : Submodule ℝ (RD d)) :
    LinearSubspaces.distSubspaces x y = distSubspacesMirror x y := by
  rfl

/-- The `planeResidualCore` of the bridge equals `Submission.ProjectionDistance.planeResidual`
(they differ only in the projection notation). -/
lemma planeResidualCore_eq_planeResidual (v x : Submodule ℝ (RD d)) :
    planeResidualCore v x = Submission.ProjectionDistance.planeResidual v x := by
  unfold planeResidualCore Submission.ProjectionDistance.planeResidual
  congr

/-- **Main bridge**: for `finrank v < finrank x` the challenge distance between the subspaces
equals the maximal orthogonal residual of unit vectors of `v` onto `x`. -/
theorem distSubspaces_eq_planeResidual (v x : Submodule ℝ (RD d))
    (hvx : finrank ℝ v < finrank ℝ x) (hvn : v ≠ ⊥) (hxne : x ≠ ⊥) :
    LinearSubspaces.distSubspaces v x = Submission.ProjectionDistance.planeResidual v x := by
  rw [distSubspaces_eq_mirror]
  rw [← planeResidualCore_eq_planeResidual]
  exact distSubspacesMirror_eq_planeResidualCore_of_lt (E := RD d) v x hvx hvn hxne

/-- **Upper bound** (one-sided bridge, strict case): challenge distance is at most the maximal
unit residual. -/
theorem distSubspaces_le_planeResidual (v x : Submodule ℝ (RD d))
    (hvx : finrank ℝ v < finrank ℝ x) (hvn : v ≠ ⊥) (hxne : x ≠ ⊥) :
    LinearSubspaces.distSubspaces v x ≤ Submission.ProjectionDistance.planeResidual v x := by
  rw [distSubspaces_eq_mirror]
  rw [← planeResidualCore_eq_planeResidual]
  exact distSubspacesMirror_le_planeResidualCore_of_lt (E := RD d) v x hvx hvn hxne

/-- **Main bridge, equal dimensions**: for `finrank v = finrank x` the challenge distance
between the two subspaces equals the maximal unit residual of `v` onto `x` (symmetry of the
Grassmann metric, `Commons.Analysis.InnerProductSpace.residualSup_eq_of_finrank_eq`). -/
theorem distSubspaces_eq_planeResidual_of_eq (v x : Submodule ℝ (RD d))
    (heq : finrank ℝ v = finrank ℝ x) (hvn : v ≠ ⊥) (hxn : x ≠ ⊥) :
    LinearSubspaces.distSubspaces v x = Submission.ProjectionDistance.planeResidual v x := by
  rw [distSubspaces_eq_mirror]
  -- equal dimensions: first branch of the mirror is active (sup over lines of `x`, measured to `v`)
  have hxle : finrank ℝ x ≤ finrank ℝ v := le_of_eq heq.symm
  unfold distSubspacesMirror
  rw [if_pos hxle]
  -- first-branch sup over lines of x = planeResidualCore x v
  rw [firstBranchSup_eq_planeResidualCore (a := x) (b := v) hxn hvn]
  -- planeResidualCore x v = planeResidualCore v x by the Grassmann-metric symmetry
  have hsym := Commons.Analysis.InnerProductSpace.residualSup_eq_of_finrank_eq (E := RD d) x v heq.symm
  change sSup (unitResidualSet x v) = sSup (unitResidualSet v x)
  exact hsym

/-- **Upper bound, equal dimensions**: challenge distance is at most the maximal unit residual
of `v` onto `x`. -/
theorem distSubspaces_le_planeResidual_of_eq (v x : Submodule ℝ (RD d))
    (heq : finrank ℝ v = finrank ℝ x) (hvn : v ≠ ⊥) (hxn : x ≠ ⊥) :
    LinearSubspaces.distSubspaces v x ≤ Submission.ProjectionDistance.planeResidual v x := by
  rw [distSubspaces_eq_planeResidual_of_eq v x heq hvn hxn]

/-- **Main bridge, full range**: whenever `finrank v ≤ finrank x` (and both subspaces are
nonzero), the challenge distance `distSubspaces v x` equals the maximal unit residual of `v`
onto `x`.  This covers all cases `k ≤ l` of the challenge (`k = finrank v`, `l = finrank x`). -/
theorem distSubspaces_eq_planeResidual_of_le (v x : Submodule ℝ (RD d))
    (hkl : finrank ℝ v ≤ finrank ℝ x) (hvn : v ≠ ⊥) (hxn : x ≠ ⊥) :
    LinearSubspaces.distSubspaces v x = Submission.ProjectionDistance.planeResidual v x := by
  rcases lt_or_eq_of_le hkl with hlt | heq
  · exact distSubspaces_eq_planeResidual v x hlt hvn hxn
  · exact distSubspaces_eq_planeResidual_of_eq v x heq hvn hxn

/-- **Upper bound, full range**: `LinearSubspaces.distSubspaces v x ≤ planeResidual v x`
whenever `finrank v ≤ finrank x`. -/
theorem distSubspaces_le_planeResidual_of_le (v x : Submodule ℝ (RD d))
    (hkl : finrank ℝ v ≤ finrank ℝ x) (hvn : v ≠ ⊥) (hxn : x ≠ ⊥) :
    LinearSubspaces.distSubspaces v x ≤ Submission.ProjectionDistance.planeResidual v x := by
  rw [distSubspaces_eq_planeResidual_of_le v x hkl hvn hxn]

end Submission.Bridge
