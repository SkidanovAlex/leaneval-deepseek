import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.step_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-!
# A map with a section induces an injective pullback on cohomology

If `π : X → B` has a continuous section `s` (`π ∘ s = id`), then `s^* ∘ π^* = (π ∘ s)^* = id`, so
the pullback `π^* : H^n(B;R) → H^n(X;R)` is **injective**.

This is the elementary half of the Gysin/descent argument, and it is what replaces the (invalid)
Mayer–Vietoris argument in the reduction of *stability* `c(E ⊕ ε) = c(E)` to
isomorphism-invariance of the Chern classes: the locus `A = {u ≠ 0} ⊆ E ⊕ ε ∖ 0`, on which the
tautological quotient is canonically `π^*E`, admits the section `b ↦ (b, 0, 1)`, so `π_A^*` is
injective (see `README.md` ADDENDUM 23.3).
-/

namespace Work.Thom

noncomputable section

variable {X B : Type} [TopologicalSpace X] [TopologicalSpace B]

/-- **A continuous section of `π` makes the pullback `π^*` injective.** -/
theorem injective_CohMap_of_section (π : C(X, B)) (s : C(B, X))
    (h : π.comp s = ContinuousMap.id B) (R : Type) [CommRing R] (n : ℕ) :
    Function.Injective (CohMap π R n).hom := by
  have hcomp : ∀ x : Coh R n B, (CohMap s R n).hom ((CohMap π R n).hom x) = x := by
    intro x
    rw [CohMap_comp_apply s π R n x, h, CohMap_id]
    rfl
  intro a b hab
  rw [← hcomp a, ← hcomp b, hab]

end

end Work.Thom
