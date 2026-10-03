import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

namespace Work.ORBassSerre.Tree.Map

open Quiver

/-- The image of the reversal of a path under a prefunctor preserving reversal is the reversal
of the image. -/
theorem qpath_mapPath_reverse {V W : Type*} [Quiver V] [Quiver.HasReverse V] [Quiver W]
    [Quiver.HasReverse W] (F : V ⥤q W) [F.MapReverse] {a b : V} (p : Quiver.Path a b) :
    F.mapPath p.reverse = (F.mapPath p).reverse := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Quiver.Path.reverse, Prefunctor.mapPath_cons, Prefunctor.mapPath_comp,
      Prefunctor.mapPath_toPath, Prefunctor.map_reverse, ih]

end Work.ORBassSerre.Tree.Map
