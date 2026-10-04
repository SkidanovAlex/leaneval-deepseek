import Mathlib
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.frobDot_rot
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.onFrame_orthogonal_change

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Frame independence of the Frobenius distance to an `O(n)`-invariant family

The frozen `CurvIn g F` (resp. the pinching hypothesis) asks for membership of the curvature
components in *every* orthonormal frame; the corresponding maximum-principle quantity is the
Frobenius distance `frobInfDist (rmFrame g x e) F` to the invariant family `F`, and it must not
depend on the chosen orthonormal frame `e` at `x`.  This file proves that:

`frobInfDist (rmFrame g x e) F = frobInfDist (rmC g x) F` whenever `F` is invariant under the
`O(n)`-action `rot`.

The argument uses only two facts about `rot A` for `A ∈ O(n)`:

* it is an isometry of the Frobenius norm: `frobDist (rot A X) (rot A Y) = frobDist X Y`
  (`frobDist_rot`, from `frobDot_rot` and additivity of `rot A` in the tensor);
* consequently, for any `F` mapped into itself by `rot A`, rotating the *point* downwards can only
  decrease the distance to `F`: `frobInfDist (rot A P) F ≤ frobInfDist P F`
  (`frobInfDist_rot_le`).  Indeed, for `S ∈ F` one has
  `frobDist (rot A P) (rot A S) = frobDist P S` and `rot A S ∈ F`.

The statement is then obtained by running this one-sided inequality in *both* directions: the two
orthonormal frames `e` and `onFrame g x` are related by orthogonal matrices `A` and `B` with
`rmFrame g x e = rot A (rmC g x)` and `rmC g x = rot B (rmFrame g x e)`
(`Work.Diff.GE.onFrame_orthogonal_change` + `Work.Diff.GE.rmFrame_eq_rot`).
-/

namespace Work.Diff.MP

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.MP

variable {n : ℕ}

/-- `rot A` is additive in the tensor argument. -/
private theorem rot_sub (A : Matrix (Fin n) (Fin n) ℝ) (S T : Curv4 n) :
    rot A (S - T) = rot A S - rot A T := by
  ext i j k l
  simp only [rot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- `rot A` for an orthogonal `A` is an isometry of the Frobenius distance. -/
private theorem frobDist_rot (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (X Y : Curv4 n) :
    frobDist (rot A X) (rot A Y) = frobDist X Y := by
  have h : rot A X - rot A Y = rot A (X - Y) := (rot_sub A X Y).symm
  rw [frobDist, frobDist, frobNorm, frobNorm, h, frobDot_rot n A hA (X - Y) (X - Y)]

/-- Rotating the point by an orthogonal matrix whose action maps `F` into itself cannot increase
the Frobenius distance to `F`. -/
private theorem frobInfDist_rot_le (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (F : Set (Curv4 n))
    (hF : ∀ R ∈ F, rot A R ∈ F) (P : Curv4 n) :
    frobInfDist (rot A P) F ≤ frobInfDist P F := by
  rcases Set.eq_empty_or_nonempty F with hF0 | hFne
  · rw [hF0]
    simp only [frobInfDist, Set.image_empty, Real.sInf_empty, le_refl]
  · refine le_frobInfDist hFne (fun S hS => ?_)
    have h := frobInfDist_le (P := rot A P) (K := F) (S := rot A S) (hF S hS)
    rwa [frobDist_rot A hA P S] at h

theorem frobInfDist_rmFrame_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (F : Set (Curv4 (Module.finrank ℝ E)))
    (hFrot : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R ∈ F, rot A R ∈ F)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    frobInfDist (rmFrame g x e) F = frobInfDist (rmC g x) F := by
  obtain ⟨A, hA, hAe⟩ :=
    Work.Diff.GE.onFrame_orthogonal_change g x (onFrame g x) e
      (Work.Diff.GE.isONFrame_onFrame g x) he
  obtain ⟨B, hB, hBe⟩ :=
    Work.Diff.GE.onFrame_orthogonal_change g x e (onFrame g x) he
      (Work.Diff.GE.isONFrame_onFrame g x)
  have hA' : rmFrame g x e = rot A (rmC g x) :=
    Work.Diff.GE.rmFrame_eq_rot hLC g x (onFrame g x) e A hAe
  have hB' : rmC g x = rot B (rmFrame g x e) := by
    show rmFrame g x (onFrame g x) = rot B (rmFrame g x e)
    exact Work.Diff.GE.rmFrame_eq_rot hLC g x e (onFrame g x) B hBe
  refine le_antisymm ?_ ?_
  · rw [hA']
    exact frobInfDist_rot_le A hA F (hFrot A hA) (rmC g x)
  · rw [hB']
    exact frobInfDist_rot_le B hB F (hFrot B hB) (rmFrame g x e)

end Work.Diff.MP
