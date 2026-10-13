import Mathlib
import Submission.Work.DSF1.Sheaf.CechStruct
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Cech.isIsoDeletion_Qi
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero

/-!
# Intersections of affine opens of an affine scheme are affine (general-scheme form)

The Čech nerve of a family of opens `U : ι → X.Opens` has as its objects the finite
intersections `Eobj U n x = ∏ᶜ (U ∘ x) = ⨅ a, U (x a)`.  If `X` is affine (so that it has
affine diagonal) and all the `U i` are affine open, then so is every `Eobj U n x`.

This is the general-scheme version of `Work.DSF1.Cech.isAffineOpen_Eobj` (which is stated
for `Spec R`), used by the Čech development for an arbitrary affine scheme.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

/-- Every object of the Čech nerve of a family of affine opens of an affine scheme is
affine. -/
theorem isAffineOpen_Eobj_of {X : Scheme.{u}} [IsAffine X] {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    (x : (Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I) :
    IsAffineOpen (Work.DSF1.Cech.Eobj U n x) := by
  rw [show Work.DSF1.Cech.Eobj U n x = ∏ᶜ (U ∘ x) from rfl, piObj_eq_iInf]
  exact IsAffineOpen.iInf (fun a => hU (x a))

end Work.DSF1.Cech
