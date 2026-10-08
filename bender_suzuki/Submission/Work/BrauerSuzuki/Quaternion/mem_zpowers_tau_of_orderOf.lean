import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

/-- In a generalized quaternion group `d` with `n ≥ 3`, an element of order `2 ^ n` must be a
power of `tau`.

Indeed, by `genQuaternionData_basic` every element outside `⟨τ⟩` has order `4`, while
`orderOf g = 2 ^ n ≥ 2 ^ 3 = 8`. -/
theorem mem_zpowers_tau_of_orderOf {Q : Type*} [Group Q] [Finite Q]
    (d : Work.BrauerSuzuki.GenQuaternionData Q) (h3 : 3 ≤ d.n) {g : Q}
    (hg : orderOf g = 2 ^ d.n) : g ∈ Subgroup.zpowers d.tau := by
  by_contra hgmem
  -- every element outside `⟨τ⟩` has order `4`
  have h4 : orderOf g = 4 := ((genQuaternionData_basic d).2.2.2.2 g hgmem).1
  rw [hg] at h4
  have h8 : 8 ≤ 2 ^ d.n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ d.n := Nat.pow_le_pow_right (by norm_num) h3
  omega

end Work.BrauerSuzuki.Quaternion
