/-
# The length of the lift of a path to the cyclic cover

The lift `liftPath L p n` of a path `p : a → b` of the base graph `Γ` to the cyclic cover `Γ̃`
starts at `(a, n)` and ends at `(b, n + pathSum θ p)`, and it uses exactly one arrow of the cover
for each arrow of `p`.  This file records the resulting statement

`(liftPath L p n).length = p.length`.

The only point to note is that the defining recursion of `liftPath` (its equation lemmas
`liftPath.eq_1`, `liftPath.eq_2`) expresses `liftPath` at `nil` and at `cons` as a *cast* along the
equality of level expressions, so the induction is run against the `Quiver.Path.cast` form of those
equations -- `liftPath_nil_cast` and `liftPath_cons_cast` from
`Submission/Work/ORLocInd/Howie/liftPath_arrowList.lean` -- together with the easy fact that casting
a path along equalities of its endpoints does not change its length.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverGraph
import Submission.Work.ORLocInd.Howie.liftPath_arrowList

set_option autoImplicit false

universe u

namespace Work.ORLocInd.Howie

/-- Casting a path along equalities of its endpoints does not change its length. -/
theorem path_length_cast {U : Type*} [Quiver U] {u v u' v' : U}
    (hu : u = u') (hv : v = v') (p : Quiver.Path u v) :
    (p.cast hu hv).length = p.length := by
  cases hu
  cases hv
  rfl

theorem liftPath_length {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Work.ORLocInd.Howie.Labelling V) {a b : V} (p : Quiver.Path a b) (n : ℤ) :
    (Work.ORLocInd.Howie.liftPath L p n).length = p.length := by
  induction p with
  | nil =>
    rw [liftPath_nil_cast L _ n, path_length_cast]
    simp
  | cons p e ih =>
    rw [liftPath_cons_cast L p e n, path_length_cast]
    show (liftPath L p n).length + 1 = (p.cons e).length
    rw [Quiver.Path.length_cons, ih]

end Work.ORLocInd.Howie
