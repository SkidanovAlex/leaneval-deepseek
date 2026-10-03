import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

namespace Work.ORBassSerre.Path.Reduction

/-- A path immediately followed by its reverse is null-reducible. -/
theorem reducesTo_nil_comp_reverse {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {a b : V} (d : Quiver.Path a b) :
    (d.comp d.reverse).ReducesTo Quiver.Path.nil := by
  induction d with
  | nil => exact Quiver.Path.ReducesTo.refl _
  | cons p e ih =>
    -- `(p.cons e).reverse = (Quiver.reverse e).toPath.comp p.reverse`, so the path
    -- `d.comp d.reverse` ends with the backtrack `e` followed by `reverse e`; deleting it
    -- leaves `p.comp p.reverse`, to which the induction hypothesis applies.
    have step : Quiver.Path.DeleteBacktrack ((p.cons e).comp (p.cons e).reverse)
        (p.comp p.reverse) := by
      have h1 : (p.cons e).reverse = (Quiver.reverse e).toPath.comp p.reverse := rfl
      have h2 : (p.cons e) = p.comp e.toPath := rfl
      rw [h1, h2, Quiver.Path.comp_assoc]
      exact Quiver.Path.DeleteBacktrack.intro p e p.reverse
    exact (Quiver.Path.ReducesTo.tail (Quiver.Path.ReducesTo.refl _) step).trans ih

end Work.ORBassSerre.Path.Reduction
