import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

namespace Work.ORBassSerre.Path.Map

open Quiver

/-- A prefunctor preserving reversal maps a single backtrack deletion to a backtrack deletion. -/
theorem deleteBacktrack_mapPath {V W : Type*} [Quiver V] [Quiver.HasReverse V] [Quiver W]
    [Quiver.HasReverse W] (F : V ⥤q W) [F.MapReverse] {a b : V} {u v : Quiver.Path a b}
    (h : Quiver.Path.DeleteBacktrack u v) :
    Quiver.Path.DeleteBacktrack (F.mapPath u) (F.mapPath v) := by
  cases h with
  | intro p₁ e p₂ =>
    simp only [Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath, Prefunctor.map_reverse]
    exact Quiver.Path.DeleteBacktrack.intro (F.mapPath p₁) (F.map e) (F.mapPath p₂)

/-- A prefunctor preserving reversal maps backtrack deletions to backtrack deletions, hence preserves the relation `ReducesTo`. -/
theorem reducesTo_mapPath {V W : Type*} [Quiver V] [Quiver.HasReverse V] [Quiver W]
    [Quiver.HasReverse W] (F : V ⥤q W) [F.MapReverse] {a b : V} {u v : Quiver.Path a b}
    (h : u.ReducesTo v) : (F.mapPath u).ReducesTo (F.mapPath v) := by
  induction h with
  | refl => exact Quiver.Path.ReducesTo.refl _
  | tail _ hstep ih => exact Quiver.Path.ReducesTo.tail ih (deleteBacktrack_mapPath F hstep)

end Work.ORBassSerre.Path.Map
