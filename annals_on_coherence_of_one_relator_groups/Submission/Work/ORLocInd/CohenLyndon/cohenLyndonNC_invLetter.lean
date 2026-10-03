import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.cohenLyndonNC_mulEquiv
import Submission.Work.ORLocInd.CohenLyndon.cohenLyndonNC_generator

set_option autoImplicit false
set_option linter.dupNamespace false

universe u

namespace Work.ORLocInd.CohenLyndon

/-! ## The "letterwise inversion" automorphism of a free group

`FreeGroup α` is free on `α`, so the assignment `of a ↦ (of a)⁻¹` extends to a group endomorphism
`letterInv`; since it is an involution it is in fact an automorphism, `letterInvEquiv`.  We need it
because the two free generators `of a` and `(of a)⁻¹` of `FreeGroup α` are *not* conjugate in
`FreeGroup α` (they are conjugate in the free *product* `FreeGroup α ∗ ℤ`), so the automorphism
invariance of `CohenLyndonNC` (`cohenLyndonNC_mulEquiv`) rather than its conjugation invariance
(`cohenLyndonNC_conj`) is the tool that transfers the property from `of a` to `(of a)⁻¹`. -/

/-- The unique group homomorphism `FreeGroup α →* FreeGroup α` sending each free generator `of a` to
its inverse `(of a)⁻¹` (the map which inverts every letter of a word, in place). -/
noncomputable def letterInv (α : Type u) : FreeGroup α →* FreeGroup α :=
  FreeGroup.lift (fun a => (FreeGroup.of a)⁻¹)

@[simp]
lemma letterInv_apply_of {α : Type u} (a : α) :
    letterInv α (FreeGroup.of a) = (FreeGroup.of a)⁻¹ := by
  simp [letterInv, FreeGroup.lift_apply_of]

/-- `letterInv` is an involution. -/
lemma letterInv_involutive {α : Type u} (x : FreeGroup α) : letterInv α (letterInv α x) = x := by
  induction x using FreeGroup.induction_on with
  | one => simp
  | of a => simp [letterInv_apply_of]
  | inv_of a _ => simp
  | mul x y ihx ihy => simp [ihx, ihy]

/-- The letterwise inversion of a free group, as a group automorphism. -/
noncomputable def letterInvEquiv (α : Type u) : FreeGroup α ≃* FreeGroup α :=
  MulEquiv.ofBijective (letterInv α)
    ⟨fun x y hxy => by
        have h := congrArg (letterInv α) hxy
        simpa [letterInv_involutive] using h,
      fun x => ⟨letterInv α x, by simp [letterInv_involutive]⟩⟩

lemma letterInvEquiv_apply {α : Type u} (x : FreeGroup α) :
    letterInvEquiv α x = letterInv α x := rfl

@[simp]
lemma letterInvEquiv_apply_of {α : Type u} (a : α) :
    letterInvEquiv α (FreeGroup.of a) = (FreeGroup.of a)⁻¹ := by
  rw [letterInvEquiv_apply, letterInv_apply_of]

/-- **A negative free generator is Cohen--Lyndon aspherical.**  The automorphism `letterInvEquiv`
of `FreeGroup α` takes the free generator `of a` to its inverse, and `CohenLyndonNC` is invariant
under group isomorphisms (`cohenLyndonNC_mulEquiv`), so the statement follows from the base case
`cohenLyndonNC_generator` for a free generator. -/
theorem cohenLyndonNC_invLetter {α : Type u} (a : α) :
    Work.CohenLyndon.CohenLyndonNC ((FreeGroup.of a)⁻¹) := by
  have h := (cohenLyndonNC_mulEquiv (letterInvEquiv α) (FreeGroup.of a)).mp
    (cohenLyndonNC_generator a)
  rwa [letterInvEquiv_apply_of a] at h

end Work.ORLocInd.CohenLyndon
