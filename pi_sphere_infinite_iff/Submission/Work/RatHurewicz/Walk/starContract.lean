import Mathlib
import Submission.Work.RatHurewicz.collapseClassOne

/-!
# The star contract: a map into a cube that touches a fixed point in two coordinates
is straight-line homotopic to that point

Let `v ∈ I^{n+2}` be a vertex-like point and `f : Y → I^{n+2}` a continuous map such that at every
`y` the point `f y` agrees with `v` in at least two distinct coordinates.  Then the coordinatewise
straight-line homotopy `H(y,t) = (1-t)·f y + t·v` runs from `f` to the constant map at `v`, and --
crucially for the applications -- *every* intermediate slice `H(y,t)` again agrees with `v` in those
same two coordinates: a coordinate in which `f y` already equals `v` is unchanged by the
interpolation.

This is the "walk" step used in the relative Hurewicz argument: the set `InSkel` is precisely the
set of points of the cube agreeing with the skeleton point `v` in two coordinates, and this lemma
shows that the straight-line homotopy of a map into `InSkel` stays inside `InSkel`, so that the
homotopy can be used in the relative setting.
-/

open scoped unitInterval Topology

namespace Work.RatHurewicz.Walk

open Work.Stems.Cubical

noncomputable section

/-- The coordinatewise straight-line homotopy from `f` to the constant map at `v`, as a continuous
map `Y × I → I^n`. -/
noncomputable def starHom {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (f : ContinuousMap Y (IC n)) (v : IC n) : ContinuousMap (Y × unitInterval) (IC n) where
  toFun p := Work.RatHurewicz.segPt (f p.1) v p.2
  continuous_toFun := by
    refine continuous_pi (fun i => ?_)
    apply Continuous.subtype_mk
    fun_prop

@[simp] theorem starHom_apply {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (f : ContinuousMap Y (IC n)) (v : IC n) (y : Y) (t : unitInterval) :
    starHom f v (y, t) = Work.RatHurewicz.segPt (f y) v t := rfl

/-- A coordinate in which `a` and `b` already agree is left fixed by the straight-line segment
from `a` to `b`. -/
theorem segPt_coord_eq_right {n : ℕ} (a b : IC n) (s : unitInterval) (j : Fin n)
    (h : a j = b j) : Work.RatHurewicz.segPt a b s j = b j := by
  apply Subtype.ext
  simp only [Work.RatHurewicz.segPt]
  rw [show ((a j : unitInterval) : ℝ) = ((b j : unitInterval) : ℝ) from by rw [h]]
  ring

theorem starContract {Y : Type} [TopologicalSpace Y] (n : ℕ)
    (v : Work.Stems.Cubical.IC (n + 2))
    (f : ContinuousMap Y (Work.Stems.Cubical.IC (n + 2)))
    (hf : ∀ y, ∃ j j' : Fin (n + 2), j ≠ j' ∧ f y j = v j ∧ f y j' = v j') :
    ∃ H : ContinuousMap (Y × unitInterval) (Work.Stems.Cubical.IC (n + 2)),
      (∀ y, H (y, 0) = f y) ∧ (∀ y, H (y, 1) = v) ∧
      (∀ y t, H (y, t) = Work.RatHurewicz.segPt (f y) v t) ∧
      (∀ y t, ∃ j j' : Fin (n + 2), j ≠ j' ∧ H (y, t) j = v j ∧ H (y, t) j' = v j') := by
  refine ⟨starHom f v, ?_, ?_, ?_, ?_⟩
  · intro y
    exact Work.RatHurewicz.segPt_zero (f y) v
  · intro y
    exact Work.RatHurewicz.segPt_one (f y) v
  · intro y t
    rfl
  · intro y t
    obtain ⟨j, j', hne, hj, hj'⟩ := hf y
    exact ⟨j, j', hne, segPt_coord_eq_right (f y) v t j hj,
      segPt_coord_eq_right (f y) v t j' hj'⟩

end

end Work.RatHurewicz.Walk
