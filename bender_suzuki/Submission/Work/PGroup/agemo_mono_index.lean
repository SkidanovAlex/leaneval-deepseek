import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- `℧ⁱ⁺¹(P) ≤ ℧ⁱ(P)`: the `p ^ (i+1)`-th powers of elements of `P` are `p ^ i`-th powers of
elements of `P`, namely of the `p`-th powers, so they generate a subgroup of `℧ⁱ(P)`. -/
theorem agemo_mono_index {G : Type*} [Group G] (p i : ℕ) (P : Subgroup G) :
    Work.PGroup.agemo p (i + 1) P ≤ Work.PGroup.agemo p i P := by
  rw [agemo, Subgroup.closure_le]
  rintro y ⟨x, hx, rfl⟩
  have heq : x ^ (p ^ (i + 1)) = (x ^ p) ^ (p ^ i) := by
    rw [pow_succ, Nat.mul_comm, pow_mul]
  rw [heq]
  exact pow_mem_agemo (p := p) (i := i) (P := P) (P.pow_mem hx p)

end Work.PGroup
