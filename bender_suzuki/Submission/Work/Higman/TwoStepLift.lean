/-
Copyright (c) 2024. All rights reserved.

# Lifting a two-step model along `ULift`

`TwoStepModel P` is universe-polymorphic in the universes of its fields `V`, `W`, so a model
built at the lowest universe has to be lifted to the universes requested by the ambient goal.

This file provides:

* `Work.Higman.AddExpTwo.ulift` -- `AddExpTwo (ULift X)` from `AddExpTwo X`;
* `Work.Higman.biadd_ulift` -- `Biadd` is preserved by the coordinatewise lift of a cocycle;
* `Work.Higman.twoStepULiftMulEquiv` -- the coordinatewise `ULift` map is an isomorphism of
  two-step groups.
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.Higman

variable {A Z : Type*}

instance (priority := 100) AddExpTwo.ulift {X : Type*} [AddCommGroup X] [AddExpTwo X] :
    AddExpTwo (ULift X) :=
  ⟨fun x => by apply ULift.ext; simpa [ULift.add_down] using AddExpTwo.add_self x.down⟩

/-- The coordinatewise `ULift` of a biadditive cocycle is biadditive. -/
theorem biadd_ulift [AddCommGroup A] [AddCommGroup Z] (b : A → A → Z) [Biadd b] :
    Biadd (fun x y : ULift A => ULift.up (b x.down y.down)) := by
  constructor
  · intro x x' y
    apply ULift.ext
    simp only [ULift.add_down]
    exact Biadd.add_left (b := b) x.down x'.down y.down
  · intro x y y'
    apply ULift.ext
    simp only [ULift.add_down]
    exact Biadd.add_right (b := b) x.down y.down y'.down

/-- The coordinatewise `ULift` map is an isomorphism of two-step groups. -/
def twoStepULiftMulEquiv [AddCommGroup A] [AddExpTwo A] [AddCommGroup Z] [AddExpTwo Z]
    (b : A → A → Z) [Biadd b] :
    TwoStep (ULift A) (ULift Z) (fun x y : ULift A => ULift.up (b x.down y.down)) ≃*
      TwoStep A Z b :=
  letI : Biadd (fun x y : ULift A => ULift.up (b x.down y.down)) := biadd_ulift b
  { toFun := fun x => ⟨x.fst.down, x.snd.down⟩
    invFun := fun x => ⟨ULift.up x.fst, ULift.up x.snd⟩
    left_inv := fun x => by apply TwoStep.ext_iff <;> simp
    right_inv := fun x => by apply TwoStep.ext_iff <;> simp
    map_mul' := fun x y => by
      apply TwoStep.ext_iff
      · simp [TwoStep.fst_mul, ULift.add_down]
      · simp [TwoStep.snd_mul, ULift.add_down] }

end Work.Higman
