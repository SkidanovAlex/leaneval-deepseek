import Mathlib
import Submission.Work.Smooth.JordanSeparation.gridWalk_approx
import Submission.Work.Smooth.JordanSeparation.gridWalk_lift
import Submission.Work.Smooth.JordanSeparation.plWalk
import Submission.Work.Smooth.JordanSeparation.simplyConnectedSpace_onePoint_complex

/-!
# The polygonal approximation of a loop in an open set (step (a))

* `joinNat` — the recursive join of a sequence of paths `Path (p k) (p (k+1))`;
* `joinNat_congr` — homotopic families give homotopic joins;
* `homotopic_restr_joinNat` — a path is homotopic to the join of its restrictions to a partition;
* `PLWalk` (redefined with an `ℕ`-indexed vertex sequence) and `exists_plWalk_freeHomotopic` —
  a loop in an open `U ⊆ ℂ` is freely homotopic, through a homotopy with values in `U`, to the
  realization of a polygonal loop through points of its trace.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-! ### The recursive join of a sequence of paths -/

/-- The recursive join of a sequence of paths `F k : Path (p k) (p (k+1))`. -/
def joinNat {X : Type*} [TopologicalSpace X] {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) :
    ∀ j : ℕ, Path (p 0) (p j)
  | 0 => Path.refl _
  | j + 1 => (joinNat F j).trans (F j)

/-- Homotopic families of paths have homotopic joins. -/
theorem joinNat_congr {X : Type*} [TopologicalSpace X] {p : ℕ → X}
    {F G : ∀ k, Path (p k) (p (k + 1))} (h : ∀ k, Path.Homotopic (F k) (G k)) :
    ∀ j, Path.Homotopic (joinNat F j) (joinNat G j)
  | 0 => Path.Homotopic.refl _
  | j + 1 => by
    rw [show joinNat F (j + 1) = (joinNat F j).trans (F j) from rfl,
      show joinNat G (j + 1) = (joinNat G j).trans (G j) from rfl]
    exact Path.Homotopic.hcomp (joinNat_congr h j) (h j)

/-- **A path is homotopic to the join of its restrictions to a partition of the unit interval.** -/
theorem homotopic_restr_joinNat {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (t : ℕ → unitInterval) :
    ∀ j, Path.Homotopic (γ.restr (t 0) (t j))
      (joinNat (p := fun i => γ (t i)) (fun k => γ.restr (t k) (t (k + 1))) j)
  | 0 => by rw [Path.restr_same]; exact Path.Homotopic.refl _
  | j + 1 => by
    rw [show joinNat (p := fun i => γ (t i)) (fun k => γ.restr (t k) (t (k + 1))) (j + 1)
        = (joinNat (p := fun i => γ (t i)) (fun k => γ.restr (t k) (t (k + 1))) j).trans
          (γ.restr (t j) (t (j + 1))) from rfl]
    exact (Path.homotopic_restr_trans γ (t 0) (t j) (t (j + 1))).trans
      (Path.Homotopic.hcomp (homotopic_restr_joinNat γ t j) (Path.Homotopic.refl _))

end

end Work.Smooth.JordanSeparation
