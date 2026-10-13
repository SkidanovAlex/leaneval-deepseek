import Mathlib
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Cech.isIsoDeletion_Qi
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero

/-!
# Intersections of affine opens of `Spec R` are affine

The Čech nerve of a family of opens `U : ι → (Spec R).Opens` has as its objects the finite
intersections `Eobj U n x = ∏ᶜ (U ∘ x) = ⨅ a, U (x a)` (`piObj_eq_iInf`).  If all the `U i`
are affine open, then so is every `Eobj U n x`: this is the fact that `Spec R` is separated
(its diagonal is an affine morphism, which `inferInstance` provides), so Mathlib's
`IsAffineOpen.iInf` applies.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

/-- Every object of the Čech nerve of a family of affine opens of `Spec R` is affine. -/
theorem isAffineOpen_Eobj (R : Type u) [CommRing R] {ι : Type u}
    (U : ι → (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens)
    (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (n : ℕ)
    (x : (Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I) :
    AlgebraicGeometry.IsAffineOpen (Work.DSF1.Cech.Eobj U n x) := by
  rw [show Work.DSF1.Cech.Eobj U n x = ∏ᶜ (U ∘ x) from rfl, piObj_eq_iInf]
  exact IsAffineOpen.iInf (fun a => hU (x a))

end Work.DSF1.Cech
