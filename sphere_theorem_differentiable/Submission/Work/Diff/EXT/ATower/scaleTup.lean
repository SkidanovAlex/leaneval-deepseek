import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.ConnCov.RicFlip.HonestTower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Slotwise scaling of a tuple of tangent fields

`scaleTup c F` is the tuple `(fun j => fun y => c j • F j y)`: the `j`-th slot of `F` scaled by the
constant `c j`.  It is the object of the *multi-homogeneity* of the packed Ricci tower
(`Work.Diff.EXT.ATower.pDiter2_multi_homog`), which in turn is the hypothesis of the
"sharpening" passage from the monotone slot bound `AMB.Bnd1` to the sharp product bound
(`Work.Diff.EXT.ConnCov.sharp_of_bnd1_homog`).

The definition is isolated in this small module so that a lemma stated in terms of it can be
delegated without the (fiber-`SMul`) instance-synthesis problems of a bare harness file.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Slotwise scaling**: the tuple whose `j`-th slot is the `j`-th slot of `F` scaled by `c j`. -/
noncomputable def scaleTup {N : ℕ} (c : Fin N → ℝ) (F : Fin N → TF (I := I) (M := M)) :
    Fin N → TF (I := I) (M := M) :=
  fun j => fun y => c j • F j y

@[simp] theorem scaleTup_apply {N : ℕ} (c : Fin N → ℝ) (F : Fin N → TF (I := I) (M := M))
    (j : Fin N) (y : M) : scaleTup (I := I) (M := M) c F j y = c j • F j y := rfl

/-- A slotwise scaling of a tuple of smooth fields is smooth. -/
theorem smE_scaleTup {N : ℕ} (c : Fin N → ℝ) {F : Fin N → TF (I := I) (M := M)}
    (hF : ∀ j, SmE I M (F j)) : ∀ j, SmE I M (scaleTup (I := I) (M := M) c F j) := by
  intro j
  have h : scaleTup (I := I) (M := M) c F j
      = (fun _ : M => c j) • F j := rfl
  rw [h]
  exact (contMDiff_const (c := c j)).smul_section (I := I) (F := E)
    (V := fun y : M => TangentSpace I y) (s := F j) (hF j)

end Work.Diff.EXT.ATower
