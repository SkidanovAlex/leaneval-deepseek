/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The connecting map `δ : Ĥ⁻¹(G, C) → Ĥ⁰(G, A)`

For a short exact sequence of `G`-modules `0 → A --f--> B --g--> C → 0` (a `Work.Tate.SES`)
the connecting homomorphism

`δ : Ĥ⁻¹(G, C) → Ĥ⁰(G, A)`

is defined on a class represented by `c ∈ ker N_C` by lifting `c` to `b ∈ B`, observing that
`N_B b ∈ ker g = im f`, writing `N_B b = f a` and taking the class of `a ∈ A^G` in `A^G/N(A)`.

This file packages the explicit construction `Work.Tate.SES.deltaLiftFun` into an additive
homomorphism `Work.Tate.SES.deltaLift` on the kernel of `N_C` and into the connecting map
`Work.Tate.SES.delta` on `Ĥ⁻¹(G, C)`.
-/
import Mathlib
import Submission.Work.Tate.SES
import Submission.Work.Tate.deltaLiftFun_zero
import Submission.Work.Tate.deltaLiftFun_add
import Submission.Work.Tate.deltaLiftFun_eq_zero_of_mem_augmentation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.Tate

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x} [Group G] [AddCommGroup A]
  [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
  [DistribMulAction G C] [Fintype G]

/-- The connecting construction as an additive homomorphism `ker N_C → Ĥ⁰(G, A)`. -/
noncomputable def SES.deltaLift (S : SES G A B C) : (norm G C).ker →+ H0 G A where
  toFun := S.deltaLiftFun
  map_zero' := deltaLiftFun_zero S
  map_add' c₁ c₂ := deltaLiftFun_add S c₁ c₂

@[simp] theorem SES.deltaLift_apply (S : SES G A B C) (c : (norm G C).ker) :
    S.deltaLift c = S.deltaLiftFun c := rfl

/-- The connecting homomorphism `δ : Ĥ⁻¹(G, C) → Ĥ⁰(G, A)`. -/
noncomputable def SES.delta (S : SES G A B C) : Hm1 G C →+ H0 G A :=
  QuotientAddGroup.lift (augInKer G C) S.deltaLift (by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    exact deltaLiftFun_eq_zero_of_mem_augmentation S hx)

@[simp] theorem SES.delta_Hm1π (S : SES G A B C) (c : (norm G C).ker) :
    S.delta (Hm1π G C c) = S.deltaLiftFun c := rfl

end Work.Tate
