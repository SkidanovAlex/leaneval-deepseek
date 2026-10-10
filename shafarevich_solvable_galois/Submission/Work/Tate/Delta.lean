import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.Tate.deltaLiftFun_add
import Submission.Work.Tate.deltaLiftFun_eq_zero_of_mem_augmentation
import Submission.Work.Tate.deltaLiftFun_zero
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
