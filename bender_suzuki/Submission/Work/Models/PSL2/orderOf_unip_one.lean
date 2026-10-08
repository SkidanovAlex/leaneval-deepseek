import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.PSL2

theorem orderOf_unip_one {F : Type*} [Field F] [CharP F 2] :
    orderOf (Work.Models.PSL2.unip (F := F) 1) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, unip_mul_self]
  · intro h
    have h01 := congrArg (fun (A : SL2 F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    rw [unip_coe] at h01
    simp at h01

end Work.Models.PSL2
