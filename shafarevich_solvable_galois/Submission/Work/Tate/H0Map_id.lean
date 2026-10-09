import Mathlib
import Submission.Work.Tate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

theorem H0Map_id {G : Type*} {A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [Fintype G] :
    Work.Tate.H0Map G A A (AddMonoidHom.id A) (fun _ _ => rfl) = AddMonoidHom.id (Work.Tate.H0 G A) := by
  ext x
  change Work.Tate.H0Map G A A (AddMonoidHom.id A) (fun _ _ => rfl) (Work.Tate.H0π G A x) =
    Work.Tate.H0π G A x
  rw [Work.Tate.H0Map_H0π]
  congr 1

end Work.Tate
