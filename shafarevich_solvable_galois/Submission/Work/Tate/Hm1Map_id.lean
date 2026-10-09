import Mathlib
import Submission.Work.Tate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- The kernel-level map induced by the identity is the identity. -/
@[simp] theorem mapKer_id {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (a : (norm G A).ker) :
    mapKer G A A (AddMonoidHom.id A) (fun _ _ => rfl) a = a :=
  Subtype.ext (mapKer_apply (AddMonoidHom.id A) (fun _ _ => rfl) a)

theorem Hm1Map_id {G : Type*} {A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [Fintype G] :
    Work.Tate.Hm1Map G A A (AddMonoidHom.id A) (fun _ _ => rfl)
      = AddMonoidHom.id (Work.Tate.Hm1 G A) := by
  apply AddMonoidHom.ext
  intro x
  induction x using Hm1_induction_on with
  | h a =>
    rw [Hm1Map_Hm1π]
    simp [mapKer_id]

end Work.Tate
